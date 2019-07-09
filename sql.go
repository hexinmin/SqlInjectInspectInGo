package main
import (
	"flag"
	"errors"
	"fmt"
	"os"
	"path"
	"strings"
	"path/filepath"
	"log"
	"container/list"
	"go/ast"
	"go/build"
	"go/token"
	
	"golang.org/x/tools/go/packages"
)

var checkDir = flag.String("dir", "", "sql injection check dir")

// getPackagePaths get path contain package from root path
func getPackagePaths(root string) ([]string, error) {
	if strings.HasSuffix(root, "...") {
		root = root[0 : len(root)-3]
	} else {
		return []string{root}, nil
	}

	paths := map[string]bool{}
	err := filepath.Walk(root, func(path string, f os.FileInfo, err error) error {
		if filepath.Ext(path) == ".go" {
			path = filepath.Dir(path)
			
			paths[path] = true
		}
		return nil
	})
	if err != nil {
		return []string{}, err
	}

	result := []string{}
	for path := range paths {
		result = append(result, path)
	}
	return result, nil
}

type functionPara struct{
	pName string
	pType string
	conflation [] *functionPara
}

func (fp *functionPara) String() string {
	s := fp.pName
	for _, p := range fp.conflation{
		s = s + "#" + (*p).String()
	}
	if s == ""{
		s = "∅"
	}
	return s
}

func (fp *functionPara) conflate(v *functionPara){
	fp.conflation = append(fp.conflation, v)
}


type StateMentAnalysis int 
const (
	_ StateMentAnalysis = iota
	StateMentAnalysis_START
	StateMentAnalysis_FUNCTION
	StateMentAnalysis_FUNCTION_BODY
)

type DbInput struct{
	format  string
	paras [] *functionPara
	next * DbInput
	follow * DbInput 
	prepare * DbInput
}

func (di *DbInput) clone() *DbInput {
	r := &DbInput{}
	*r = *di
	r.next = nil
	r.follow = nil
	r.prepare = nil
	
	return r
}

func (di *DbInput) deepclone() *DbInput {
	r := di.clone()
	rloop := r
	dfollow := di.follow
	for ; dfollow != nil; dfollow = dfollow.follow{
		rloop.follow = dfollow.clone()
		rloop = rloop.follow	
	}
	return r
}

func (di *DbInput) toStringSingle() string {
	s := ""
	if di.format == ""{
		s = "(blank)"
	}else
	{
		s = fmt.Sprintf("%d:", len(di.format))
		s += di.format
	}
	
	s = s + "" + "["
	for _, p := range di.paras{
		s = s + (*p).String() + ","
	}
	s = s + "]" //+ fmt.Sprintf("%p", di)
    return s
}

func (di *DbInput) toString() string {
	s := di.toStringSingle()
	for f := di.follow; f != nil; f = f.follow{
		s = s + "-->" + f.toStringSingle()
	}
    return s
}

func (di *DbInput) String() string {
	dump := di
	s := (*dump).toString()	
	for{
		if (*dump).next == di || (*dump).next== nil{
			break
		}
		dump = (*dump).next
		s = s + "==>" + (*dump).toString()
	}
	return s
}

func (di *DbInput) updateForAdd(){
	if di.Empty(){
		panic(1)
	}
	if len(di.paras) > 0 && ((*di).format == ""){
		s := "%s"
		di.format = s
	}
}

func (di *DbInput) Empty() bool {
	return di.format == "" && len(di.paras) == 0 && di.next == nil
}

func (di *DbInput) isCollection() bool {
	return di.next != nil
}

func (di *DbInput) appendTail(v *DbInput) *DbInput {
	// get tail
	if (*di).next == nil{
		panic(1)
	}
	tail := (*di).next
	for{
		if (*tail).next == di{
			break
		}
		tail = (*tail).next
	}
	(*tail).next = v
	(*v).next = di
	return di
}

func (di *DbInput) likeStringJoin(v *DbInput) *DbInput {
	// deep copy
	if (*di).next == nil{
		panic(1)
	}
	n1 := (*di).next
	n2 := (*n1).next
	for{
		if n1 == n2 || n2 == di{
			break
		}
		newV := &DbInput{
			format: (*v).format,
			paras : (*v).paras,
		}
		(*n1).next = newV
		(*newV).next = n2
		n1 = n2
		n2 = (*n1).next
	}
	return di
}

func (di *DbInput) filterEmptyPara(){
	c := di.getParaCountFromFormat()
	for i:= len(di.paras); i < c; i++{
		di.paras = append(di.paras, nil)
	}
}

func (di *DbInput) getParaCountFromFormat() int {
	count := 0
	var pre rune
	for i, c := range di.format{
		if i > 0 && c == '%' && pre != '\\' {
			count = count + 1
		}
		pre = c
	}
	return count
}

type FomatState int 
const (
	_ FomatState = iota
	FomatState_START
	FomatState_PERCENT
)

// getFormatPos index from 0, only for %x
func (di *DbInput) getFormatPos(index int) (int, rune, bool){
	var pre rune
	count := 0
	state := FomatState_START
	for i, c := range di.format{
		if c == '%'{
			if state == FomatState_START{
				state = FomatState_PERCENT
			}else{
				state = FomatState_START // %%
			}
		}else if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'){
			if state == FomatState_PERCENT{
				if count == index{
					return i, c, true
				}else{
					count++
					state = FomatState_START 
				}
			}
		}else{
			state = FomatState_START
		}
	}
	return 0, pre, false
}

// getFormatOrQuestionMarkPos both find %x and ? and %%s%
func (di *DbInput) getFormatOrQuestionMarkPos(index int) (int, rune, bool){
	var pre rune
	count := 0
	state := FomatState_START
	for i, c := range di.format{
		if c == '?'{
			if count == index{
				return i, c, true
			}else{
				count ++
				state = FomatState_START
			}
		}else if c == '%'{
			state = FomatState_PERCENT
		}else if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'){
			if state == FomatState_PERCENT{
				if count == index{
					return i, c, true
				}else{
					count ++
					state = FomatState_START
				}
			}
		}else
		{
			state = FomatState_START
		}
	}
	return 0, pre, false
}

func (di *DbInput) appendParas(paras [] *functionPara) {
	for _, p1 := range paras{
		found := false
		for j, p2 := range di.paras{
			if p2 == nil{
				di.paras[j] = p1
				found = true
				break
			}
		}
		if !found {
			di.paras = append(di.paras, p1)
		}
	}
}

func (di *DbInput) last()*DbInput{
	for; ; di = di.follow{
		if di.follow == nil{
			return di
		}
	}
}

func (di *DbInput) add(input *DbInput)*DbInput{
	r1 := di.deepclone()
	r2 := input.deepclone()
	r1.last().follow = r2
	return r1
}

func (di *DbInput) concat(input *DbInput)*DbInput{
	(*di).format += input.format
	di.paras = append(di.paras, input.paras...) 
	// merge paras
	return di
}

func (di *DbInput) merge() *DbInput{
	r := &DbInput{}
	n := (*di).next
	for{
		if n == nil || n == di{
			break
		}
		r = (*r).concat(n)
		n = (*n).next
	}
	return r
}

func (di *DbInput) addFormat(input *DbInput) *DbInput{
	return input.mergePureFormat().deepSplit()
}

func (di *DbInput) addFormatDb(input *DbInput) *DbInput{
	return input.mergePureFormat().deepSplitDB()
}

func (di *DbInput) mergePureFormat() *DbInput {
	r := di.deepclone()
	for l := r; l.follow != nil;{
		follow := l.follow.follow
		if len(l.paras) == 0 && len(l.follow.paras) == 0{
			l.format = l.format + l.follow.format
			l.follow = follow
		}else{
			l = l.follow
		}
	}
	return r
}

func (di *DbInput) deepSplit()*DbInput {
	r := di.split()
	l := di
	for l.follow != nil{
		r.last().follow = l.follow.split()
		l = l.follow
	}
	return r
}

func (di *DbInput) split()*DbInput {
	r := di.clone()
	if len(r.paras) > 0{
		return r
	}
	l := r 
	for{
		if i, _, ok := l.getFormatPos(0); ok{
			f := l.clone()
			lf := l.format[:i + 1]
			if lf == l.format{
				break
			}
			ff := l.format[i + 1:]
			l.format = lf
			f.format = ff
			l.follow = f
			l = f
		}else{
			break
		}
	}
	return r
}

func (di *DbInput) deepSplitDB()*DbInput {
	r := di.split()
	l := di
	for l.follow != nil{
		r.last().follow = l.follow.splitDB()
		l = l.follow
	}
	return r
}

func (di *DbInput) splitDB()*DbInput {
	r := di.clone()
	if len(r.paras) > 0{
		return r
	}
	l := r 
	for{
		if i, _, ok := l.getFormatOrQuestionMarkPos(0); ok{
			f := l.clone()
			lf := l.format[:i + 1]
			if lf == l.format{
				break
			}
			ff := l.format[i + 1:]
			l.format = lf
			f.format = ff
			l.follow = f
			l = f
		}else{
			break
		}
	}
	return r
}

func (di *DbInput) getFirstEmpty()*DbInput {
	l := di
	for l!= nil{
		if len(l.paras) == 0 && l.prepare == nil{
			return l
		}else{
			l = l.follow
		}
	}
	return nil
}

func (di *DbInput) addParameter(input *DbInput) *DbInput{
	if (*input).next == nil{
		return di.addParameterSingle(input)
	}else{
		n := (*input).next
		for{
			if n == input{
				break
			}
			di = di.addParameterSingle(n)
			n = (*n).next
		}
		return di
	}
}

// addParameterSingle for sprintf
func (di *DbInput) addParameterSingle(input *DbInput) *DbInput{
	prepare := di.getFirstEmpty()
	if prepare == nil{
		panic(1)
	}
	prepare.prepare = input.deepclone()
	return di
}

func (di *DbInput) commit(){
	if di.prepare != nil{
		_, c, _ := di.getFormatPos(0)
		if c == 's'{
			// replace
			di.prepare.last().follow = di.follow
			f := di.prepare.follow
			format := di.format[:len(di.format) - 2] + di.prepare.format
			*di = *(di.prepare)
			di.follow = f
			di.format = format
		}else{
			di.prepare = nil
			di.paras = [] *functionPara {}
		}
	}
}

func (di *DbInput) commitDB(){
	if di.prepare != nil{
		_, c, _ := di.getFormatOrQuestionMarkPos(0)
		if c == 's'{
			// replace
			di.prepare.last().follow = di.follow
			f := di.prepare.follow
			format := di.format[:len(di.format) - 2] + di.prepare.format
			*di = *(di.prepare)
			di.follow = f
			di.format = format
		}else{
			di.prepare = nil
			di.paras = [] *functionPara {}
		}
	}
}

func (di *DbInput) deepCommit(){
	l := di
	f := l.follow
	for ; l != nil ; l = f{
		l.commit()
		f = l.follow
	}
}

func (di *DbInput) deepCommitDB(){
	l := di
	f := l.follow
	for ; l != nil ; l = f{
		l.commitDB()
		f = l.follow
	}
}

func (di *DbInput) reportError(fun string, paras [] functionPara)string{
	s := ""
	if di.Empty(){
		return s
	}

	for i := 0; ; i ++{
		if _, c, ok := di.getFormatOrQuestionMarkPos(i); ok{
			if c == 's' && i < len(di.paras){
				for _, p := range(paras){
					if di.paras[i] != nil && di.paras[i].pName == p.pName{
						s = fun + " exist sql injection" 
						return s
					}
				}
			}
			// check
		}else{
			break
		}

	}
	return s
}

type ExtraceName struct {
	result  string
	selectFlag bool
	caseStack   *list.List
}

func NewExtraceName() *ExtraceName{
	return &ExtraceName{
		selectFlag : false,
		caseStack:   list.New(),}
}

func (en *ExtraceName) Visit(n ast.Node) ast.Visitor {
	if n == nil{
		en.upDateStateAfterPop()
		return nil
	} else {
		en.caseStack.PushBack(n)
		switch t:= n.(type){
		case *ast.Ident:{
				en.result = en.result + t.Name
			}
		case *ast.StarExpr:{
				en.result = en.result + "*"
			}
		case *ast.ArrayType:{
				en.result = en.result + "[]"
			}
		case *ast.SelectorExpr:{
			en.selectFlag = true
		}
		}
	}
	return en
}

func (en *ExtraceName) upDateStateAfterPop(){
	e := en.caseStack.Back()
	en.caseStack.Remove(e)
	if last := en.caseStack.Back(); last != nil{
		if _, ok := last.Value.(*ast.SelectorExpr); ok{
			if en.selectFlag{
				en.result = en.result + "."
				en.selectFlag = false
			}
		}
	}
}

type Analyzer struct {
	ignoreNosec bool
	catchError bool
	caseStack   *list.List
	parameters  [] functionPara
	curParaName   string
	curParaType   string
	state       StateMentAnalysis
	curFunName    string
	logger      *log.Logger
	dbCallPara   map[string]string
	allPossibleInput map[string] *DbInput
	result [] string
}

func (si *Analyzer) isFunctionParaName() bool {
	last := si.caseStack.Back() // type is []*ast.Ident
	if last = last.Prev(); last != nil{
		switch last.Value.(type){
		case *ast.FieldList:
			if last = last.Prev(); last != nil{
				switch last.Value.(type){
				case *ast.FuncType:
					if last = last.Prev(); last != nil{
						switch last.Value.(type){
						case *ast.FuncDecl:
							return true
						}
					}
				}
			}
		}
	}	
	return false
}

func (si *Analyzer) isFunctionBlockStmt() bool {
	last := si.caseStack.Back() // type is *ast.BlockStmt
	if last = last.Prev(); last != nil{
		switch last.Value.(type){
		case *ast.FuncDecl:{
				return true
			}	
		default:
			
		}
	}
	return false
}

func (si *Analyzer) isSprintfCall(n ast.Node) bool{
	switch node:= n.(type){
	case *ast.CallExpr:
		//switch f := node.Fun.(type){
		switch node.Fun.(type){
		case *ast.SelectorExpr:
			return true
			//if f.Sel.Name == "Sprintf"{
			//	return true
			//}
		}
	}
	return false
}

func (si *Analyzer) ChangeState(s StateMentAnalysis){
	//fmt.Println("state change from  " , si.state, " to ", s)
	si.state = s
}

// todo : delete
func getParaType(f ast.Field) string {
	result := ""
	switch t:= f.Type.(type){
	case *ast.Ident:{
			return t.Name
		}
	case *ast.StarExpr:{
			result = "*"
			switch seType:= t.X.(type){
			case *ast.SelectorExpr:
				switch xt:= seType.X.(type){
				case *ast.Ident:
					result = result + xt.Name
				default:
					panic(xt)
				}
				result = result + "." + seType.Sel.Name
			}
		}
	case *ast.SelectorExpr:{
		switch xt:= t.X.(type){
		case *ast.Ident:
			result = result + xt.Name
		default:
			panic(xt)
		}
		result = result + "." + t.Sel.Name
	}
	case *ast.ArrayType:{
		switch Elt := t.Elt.(type){
		case *ast.Ident:{
			result = result + "[]" + Elt.Name
		}
	default:
			panic(Elt)
		}
	}
	default:
		panic(t)
	}

	return result
} 

func (si *Analyzer) upDateStateAfterPop(){
	lastElement := si.caseStack.Back()
	switch lastElement.Value.(type){
	case *ast.BlockStmt:{
			if si.isFunctionBlockStmt() && 
				si.state == StateMentAnalysis_FUNCTION_BODY{
				si.ChangeState(StateMentAnalysis_FUNCTION)
			}
		}
	case *ast.FuncDecl:{
			if si.state == StateMentAnalysis_FUNCTION{
				si.parameters = nil
				si.curFunName = ""
				si.allPossibleInput = make(map[string] *DbInput)
				si.dbCallPara = make(map[string]string)
				si.ChangeState(StateMentAnalysis_START)
			}
		}
	}
	si.caseStack.Remove(lastElement)
}

func isStringFormat(str string, pos int) bool{
	count := 0
	for i:= 0; i + 1 < len(str); i++{
		if str[i] == '%'{
			count++
		}

		if count == pos{
			if str[i] == 's'{
				return true
			}
		}
	}

	return false
}

func (si *Analyzer) isFunctionParameters(v string) bool{
	for _, para := range si.parameters{
		if para.pName == v{
			return true
		}
	}

	return false
}

func (si *Analyzer) isDbCallFunction() bool{
	for _, para := range si.parameters{
		if para.pType == "*sqlx.DB" ||
			para.pType == "kitSql.DbInterface" {
			return true
		}
	}
	return false
}

func (si *Analyzer) getDbInputFromToken(token string) *DbInput {
	if k, ok := si.allPossibleInput[token]; ok{
		return k
	} else {
		return &DbInput{
			format : "%s",
			paras: [] *functionPara {&functionPara{pName:token,},},
		}
	}
}

func (si *Analyzer) getDbInputFromRhs(n ast.Node) *DbInput {
	di := &DbInput{}
	// fmt.printf
	if callexp, ok := n.(*ast.CallExpr); ok {
		if f, ok := callexp.Fun.(*ast.SelectorExpr); ok{
			if x, ok := f.X.(*ast.Ident); ok {
				if x.Name == "fmt" && f.Sel.Name == "Sprintf"{
					// deal format
					for i, arg := range callexp.Args{
						if i == 0{
							// ad format
							addFormat := si.getDbInputFromRhs(arg)
							di = di.addFormat(addFormat)
						} else {
							// add parameter
							addParameter := si.getDbInputFromRhs(arg)
							di = di.addParameter(addParameter)
						}
					}
					di.deepCommit()
				} else if x.Name == "strings" && f.Sel.Name == "Join"{
					di = si.getDbInputFromRhs(callexp.Args[0])
					if !di.isCollection(){ // todo delete
						di = &DbInput{}
						(*di).next = di
					}
					join := si.getDbInputFromRhs(callexp.Args[1])
					(*di).likeStringJoin(join)
					di = di.merge()
				}
			}
		} else if f, ok := callexp.Fun.(*ast.Ident); ok{
			if f.Name == "append"{
				for i, arg := range callexp.Args{
					if i == 0{
						di = si.getDbInputFromRhs(arg)
						if !di.isCollection(){ // todo delete
							di = &DbInput{}
							(*di).next = di
						}
					} else {
						new := si.getDbInputFromRhs(arg)
						(*di).appendTail(new)
					}
				}
			}
		}
	}else if v, ok := n.(*ast.BinaryExpr); ok {
		if v.Op == token.ADD{
			X := si.getDbInputFromRhs(v.X)
			Y := si.getDbInputFromRhs(v.Y)
			di = X.add(Y)
		}
	}else if v, ok := n.(*ast.BasicLit); ok { // plain text
		s := v.Value
		s = s[1:len(s)-1]
		return &DbInput{
			format: s,
		}
	}else if v, ok := n.(*ast.Ident); ok{ // *ast.Ident
		if k, ok := si.allPossibleInput[v.Name]; ok{
			return k
		} else {
			return &DbInput{
				format : "%s",
				paras: [] *functionPara {&functionPara{pName:v.Name,},},
			}
		}
	}else if v, ok := n.(*ast.CompositeLit); ok{
		if Type, ok := v.Type.(*ast.ArrayType); ok{
			switch Elt := Type.Elt.(type) {
				case *ast.Ident:{
					// []string{}
					if Elt.Name == "string"{
						di = &DbInput{}
						(*di).next = di
					}	
				}
				case *ast.InterfaceType:{
					// []interface{}{}
					if !Elt.Incomplete{
						di = &DbInput{}
						(*di).next = di
					}
				}
			}
		}
	}else{
		en := NewExtraceName()
		ast.Walk(en, n)
		if en.result != ""{
			//di.paras = append(di.paras, &functionPara{pName:en.result,})
			di = si.getDbInputFromToken(en.result)
		}
	}
	// []interface{}{}
	
	// to do else
	return di
}

func (si *Analyzer) AddDbCallPara(n string, t string){
	switch t{
	case "*sqlx.DB", "*sqlx.Tx", "sql.DbInterface","kitSql.DbInterface":
		{
			if _, ok := si.dbCallPara[n]; !ok{
				si.dbCallPara[n] = t
			}
		}
	}
}

func (si *Analyzer) isDbInterfaceCall(n *ast.CallExpr) (string, string, bool) {
	if f, ok := n.Fun.(*ast.SelectorExpr); ok{
		if x, ok := f.X.(*ast.Ident); ok{
			if v, ok := si.dbCallPara[x.Name]; ok{
				return v, f.Sel.Name, true
			}
		}
	}
	return "", "", false
}

func (si *Analyzer) analyzeDbCall(di *DbInput, ce *ast.CallExpr, index int) *DbInput{
	for i, arg := range ce.Args{
		if i == index{
			addFormat := si.getDbInputFromRhs(arg)
			di = (*di).addFormatDb(addFormat)
		} else if i > index {
			addPara := si.getDbInputFromRhs(arg)
			di = (*di).addParameter(addPara)
		}
	}
	di.deepCommitDB()
	return di
}

func (si *Analyzer) checkDbCall(node *ast.CallExpr, iType string, fName string){
	di := &DbInput{}
	switch iType{
	case "*sqlx.DB":{
		switch fName{
			case "Get","Select":{
					di = si.analyzeDbCall(di, node, 1)
				}
			case "Queryx":{
				di = si.analyzeDbCall(di, node, 0)
			}
			}
		}
	case "*sqlx.Tx":{
		switch fName{
			case "Exec":{
					di = si.analyzeDbCall(di, node, 0)
				}
			case "Get":{
					di = si.analyzeDbCall(di, node, 1)
				}
			}
		}
	case "sql.DbInterface":
		switch fName{
		case "Get":{
			di = si.analyzeDbCall(di, node, 1)
		}
		}
	case "kitSql.DbInterface":{
		switch fName{
			case "Get":{
				di = si.analyzeDbCall(di, node, 1)
			}
			case "Exec":{
				di = si.analyzeDbCall(di, node, 0)
			}
			}
	}
	}	
	
	fmt.Println("final di is ")
	fmt.Println(di.toString())
	/*
	s := di.reportError(si.curFunName, si.parameters)
	if s != ""{
		fmt.Println(s)
		si.result = append(si.result, s)
	}*/
}

func (si *Analyzer) Visit(n ast.Node) ast.Visitor {
	defer func(){ 
        //fmt.Println("catch error")
        if err:=recover();err!=nil{
			fmt.Println(err) 
			si.catchError = true
        }
    }()
	if n == nil{
		si.upDateStateAfterPop()
		//fmt.Printf("pop len is %d\n", si.caseStack.Len())
		return nil
	} else {
		si.caseStack.PushBack(n)
		//fmt.Printf("push len is %d\n", si.caseStack.Len())
		switch node:= n.(type){
			case *ast.Field:
				/*
				if si.isFunctionParaName(){
					if len(node.Names) > 0{
						//fmt.Printf("%s %s\n", node.Names[0].Name, getParaType(*node))
						si.parameters = append(si.parameters, 
							functionPara{pName:node.Names[0].Name, pType:getParaType(*node)})
						si.AddDbCallPara(node.Names[0].Name, getParaType(*node))
					}
				}*/
			case *ast.FuncDecl:
				if	si.state == StateMentAnalysis_START{
					si.curFunName = node.Name.Name
					si.catchError = false
					fmt.Println("check " + si.curFunName)
					si.ChangeState(StateMentAnalysis_FUNCTION)
				}
				for _, para := range node.Type.Params.List{
					en := NewExtraceName()
					ast.Walk(en, para.Type)
					//fmt.Println("para type:", en.result)
					si.parameters = append(si.parameters, 
						functionPara{pName:para.Names[0].Name, pType:en.result})
					si.AddDbCallPara(para.Names[0].Name, en.result)
				}
			case *ast.BlockStmt:{
				if	si.state == StateMentAnalysis_FUNCTION{
					si.ChangeState(StateMentAnalysis_FUNCTION_BODY)
				}
			}
			case *ast.CallExpr:{
				//fmt.Printf("call expr %d\n", si.state )
				if si.state == StateMentAnalysis_FUNCTION_BODY && !si.catchError{

					/*
					if si.isSprintfCall(n){
						//fmt.Printf("is sprintf call\n")
						if len(node.Args) >= 2{
							switch format := node.Args[0].(type){
							case *ast.BasicLit:
								for i, para := range(node.Args){
									if i > 0{
										switch p := para.(type){
										case *ast.Ident:
											if isStringFormat(format.Value, i) && si.isFunctionParameters(p.Name) && si.isDbCallFunction(){
												fmt.Printf("sql injectiton:%s\n", si.curFunName)
											}
										}
									}
								}
							}
						}
					}*/
					
					if iType, fName, ok := si.isDbInterfaceCall(node); ok{
						si.checkDbCall(node, iType, fName)
					}
					
				}
			}
			case *ast.AssignStmt:{
				if si.state == StateMentAnalysis_FUNCTION_BODY && !si.catchError{
					// del right
					
					if node.Tok == token.ADD_ASSIGN{
						dbInput := si.getDbInputFromRhs(node.Rhs[0])
						if !dbInput.Empty(){
							if v, ok := node.Lhs[0].(*ast.Ident); ok{
								left := si.getDbInputFromRhs(node.Lhs[0])
								if !left.Empty(){
									si.allPossibleInput[v.Name] = left.add(dbInput)
									//fmt.Println("allPossibleInput add += ", v.Name, ":", left)
								}
							}
						}
					} else {
						dbInput := si.getDbInputFromRhs(node.Rhs[0])
						//fmt.Println("new input:", dbInput)
						if !dbInput.Empty(){
							if v, ok := node.Lhs[0].(*ast.Ident); ok{
								si.allPossibleInput[v.Name] = dbInput
								//fmt.Println("allPossibleInput add ", v.Name, ":", dbInput)
							}
						}
					}

				}
			}
		}
		return si
	}
}

func (si *Analyzer) check(pkg *packages.Package) {
	for _, file := range pkg.Syntax {
		//si.logger.Println("Checking file:", pkg.Fset.File(file.Pos()).Name())
		ast.Walk(si, file)
	}
}

// GetPkgAbsPath returns the Go package absolute path derived from
// the given path
func GetPkgAbsPath(pkgPath string) (string, error) {
	absPath, err := filepath.Abs(pkgPath)
	if err != nil {
		return "", err
	}
	if _, err := os.Stat(absPath); os.IsNotExist(err) {
		return "", errors.New("no project absolute path found")
	}
	return absPath, nil
}

func (si *Analyzer) load(pkgPath string, conf *packages.Config) ([]*packages.Package, error) {
	abspath, err := GetPkgAbsPath(pkgPath)
	if err != nil {
		si.logger.Printf("Skipping: %s. Path doesn't exist.", abspath)
		return []*packages.Package{}, nil
	}

	si.logger.Println("Import directory:", abspath)
	basePackage, err := build.Default.ImportDir(pkgPath, build.ImportComment)
	if err != nil {
		si.logger.Println("Import err:", err)
		return []*packages.Package{}, fmt.Errorf("importing dir %q: %v", pkgPath, err)
	}
	
	var packageFiles []string
	for _, filename := range basePackage.GoFiles {
		packageFiles = append(packageFiles, path.Join(pkgPath, filename))
	}

	/*
	if si.tests {
		testsFiles := []string{}
		testsFiles = append(testsFiles, basePackage.TestGoFiles...)
		testsFiles = append(testsFiles, basePackage.XTestGoFiles...)
		for _, filename := range testsFiles {
			packageFiles = append(packageFiles, path.Join(pkgPath, filename))
		}
	}
	*/
	
	pkgs, err := packages.Load(conf, packageFiles...)
	if err != nil {
		return []*packages.Package{}, fmt.Errorf("loading files from package %q: %v", pkgPath, err)
	}
	return pkgs, nil
}

func (gosec *Analyzer) pkgConfig(buildTags []string) *packages.Config {
	flags := []string{}
	if len(buildTags) > 0 {
		tagsFlag := "-tags=" + strings.Join(buildTags, " ")
		flags = append(flags, tagsFlag)
	}
	
	return &packages.Config{
		Mode:       packages.LoadSyntax,
		//Mode:       packages.LoadFiles,
		BuildFlags: flags,
		Tests:      false,
	}
}

func (si *Analyzer) Process(buildTags []string, packagePaths [] string) error {
	config := si.pkgConfig(buildTags)
	for _, pkgPath := range packagePaths {
		
		pkgs, err := si.load(pkgPath, config)
		if err != nil {
			//si.AppendError(pkgPath, err)
			fmt.Println(pkgPath, " load error:", err)
		}
		for _, pkg := range pkgs {
			// todo : analyze load error 
			if pkg.Name != "" {
				si.check(pkg)
			}
		}
	}
	//sortErrors(si.errors)
	return nil
}

func (si *Analyzer) CheckDir(d string) {
	paths, err:= getPackagePaths(d)
	if err != nil{
		fmt.Println(err)
	}
	var buildTags []string
	si.Process(buildTags, paths)
}

func unittest1(){
	fmt.Println("-------------------")
	s1 := "SELECT %s FROM %s b_sum"
	s2 := "%s"
	
	di1 := &DbInput{
		format: s1,
		//paras: [] *functionPara {&functionPara{pName:"p1",},},
	}

	fmt.Println("di1 :", di1)
	di1 = di1.split()
	fmt.Println("di1 :", di1)
	fmt.Println("di1 merge :", di1.mergePureFormat())

	di2 := &DbInput{
		format: s2,
		paras: [] *functionPara {&functionPara{pName:"p2",},},
	}

	fmt.Println("di2 :", di2)
	di3 := di1.add(di2)
	di4 := di3.add(di1)
	fmt.Println("di1 + di2 :", di1.add(di2))
	fmt.Println("di3 :", di3)
	fmt.Println("di4 :", di4)

	di5 := di4.deepclone()
	di4 = di4.add(di1)
	fmt.Println("di5 :", di5)
	fmt.Println("di4 :", di4)
	
	di5 = di5.add(di1)
	di5 = di5.add(di2)
	di5 = di5.add(di1)
	di6 := di5.mergePureFormat()
	fmt.Println("di5 :", di5)
	fmt.Println("di6 :", di6)
	di7 := di6.deepSplit()
	fmt.Println("di7 :", di7)
	di8 := di7.mergePureFormat()
	fmt.Println("di8 :", di8)
	di9 := di8.deepSplit()
	fmt.Println("di9 :", di9)
}

func unittest(){
	s0 := "ab???cdeft%%s%dagdsg%%d%23523?f%dsaf?%s"
	di_test := &DbInput{
		format: s0}
	fmt.Println(s0)
	for i:= 0; ;i++{
		if pos, c ,ok := (*di_test).getFormatOrQuestionMarkPos(i); ok{
			fmt.Println("pos: ", pos, " c:",string(c))
		}else{
			break
		}
	}

	fmt.Println("----------------------")

	for i:= 0; ;i++{
		if pos, c ,ok := (*di_test).getFormatPos(i); ok{
			fmt.Println("pos: ", pos, " c:",string(c))
		}else{
			break
		}
	}

	fp1 := &functionPara{pName:"fp1fp1"}
	fmt.Println("fp1 :", fp1)

	fp2 := &functionPara{pName:"fp2fp2"}
	fmt.Println("fp2 :", fp2)

	fp3 := &functionPara{pName:"fp3fp3"}
	fmt.Println("fp3 :", fp3)

	fp3.conflate(fp2)
	fp3.conflate(fp1)
	fmt.Println("new fp3 :", fp3)

	s1 := "xxx"
	s2 := "yyyy"
	s3 := "zzzz"
	di1 := &DbInput{
		format: s1,
		paras: [] *functionPara {&functionPara{pName:"xxxx",},},
	}

	fmt.Println("di1 :", di1)

	di2 := &DbInput{
		format: "",
		paras: [] *functionPara {&functionPara{pName:"xxxx",},},
	}

	fmt.Println("di2 :", di2)
	di3 := (*di1).concat(di2)
	fmt.Println("di3 :", di3)

	(*di1).next = di1
	di4 := di1.appendTail(di2)
	fmt.Println("di4 :", di4)

	di5 := &DbInput{
	}
	(*di5).next = di5

	di5 = di5.appendTail(&DbInput{
		format: s1,
		paras: [] *functionPara {&functionPara{pName:"xxxx",},},
	})
	di5 = di5.appendTail(&DbInput{
		format: s2,
		paras: [] *functionPara {&functionPara{pName:"yyyy",},},
	})
	fmt.Println("di5 :", di5)

	di6 := di5.likeStringJoin(&DbInput{
		format: s3,
		paras: [] *functionPara {&functionPara{pName:"zzz",},},
	})
	fmt.Println("di6 :", di6)

	di7 := di6.merge()
	fmt.Println("di7 :", di7)

	unittest1()
}

func main(){
	/*
	fmt.Printf("%%%s\n","xxxx")
	unittest()
	return
*/
	flag.Parse()
	si  := &Analyzer{
		catchError : false,
		logger:	log.New(os.Stderr, "[sqlinj]", log.LstdFlags),
		caseStack:   list.New(),
		//parameters:       make([]functionPara,1),
		state:       StateMentAnalysis_START,
		allPossibleInput: make(map[string]*DbInput),
		dbCallPara:       make(map[string]string),
	}
	si.CheckDir(*checkDir)
	for _, err := range si.result{
		fmt.Println("error: ", err)
	}
	//fmt.Println(getPackagePaths(*checkDir))
}
