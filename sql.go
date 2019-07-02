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
	di * DbInput
}

type StateMentAnalysis int 
const (
	_ StateMentAnalysis = iota
	StateMentAnalysis_START
	StateMentAnalysis_FUNCTION
	StateMentAnalysis_FUNCTION_BODY
)

type DbInput struct{
	format string
	paras [] *functionPara
	
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

func (di *DbInput) getFirstEmpty(start int) (int, bool){
	for i , p := range di.paras{
		if i >= start && p == nil{
			return i, true
		}
	}
	return 0, false
}

// index from 1
func (di *DbInput) getFormatPos(index int) (int, rune, bool){
	count := 1
	var pre rune
	for i, c := range di.format{
		if i > 0 && c == '%' && pre != '\\' {
			if count == index{
				return i, pre, true
			}
			count = count + 1
		}
		pre = c
	}
	return 0, pre, false
}

func (di *DbInput) addFormat(input *DbInput) *DbInput{
	di.format = input.format
	di.paras = append(input.paras, di.paras...)
	di.filterEmptyPara()
	return di
}

func (di *DbInput) addParameter(index int, input *DbInput) *DbInput{
	if input.format == ""{
		// only parameters, find place
		for _, p := range input.paras{
			if i, ok := di.getFirstEmpty(0); ok{
				di.paras[i] = p
			}else{
				panic(2)
			}
		}
	} else{
		// find format pos
		if pos, preChar, ok := di.getFormatPos(index); ok{
			if preChar == 's'{
				// merge 
				di.format = di.format[:pos - 1] + input.format
				newParas := di.paras[:index - 1]
				newParas = append(newParas, input.paras...)
				newParas = append(newParas, di.paras[index - 1:]...)
				di.paras = newParas
			}else{
				// set empty parameter
				di.paras[index - 1] = &functionPara{}
			}
			
		}else{
			panic(3)
		}
	}
	return di
}

func (di *DbInput) reportError(){
}


type Analyzer struct {
	ignoreNosec bool
	
	caseStack   *list.List
	parameters  [] functionPara
	curParaName   string
	curParaType   string
	state       StateMentAnalysis
	curFunName    string
	logger      *log.Logger
	dbCallPara   map[string]string
	allPossibleInput map[string] *DbInput
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
							di = di.addParameter(i, addParameter)
						}
					}
				}
			}
		}
	}
	// to do else
	return di
}

func (si *Analyzer) AddDbCallPara(n string, t string){
	switch t{
	case "*sqlx.DB", "sqlx.Tx":
		{
			if _, ok := si.dbCallPara[n]; !ok{
				si.dbCallPara[n] = t
			}
		}
	}
}

func (si *Analyzer) isDbInterfaceCall(n ast.Node) (string, string, bool) {
	if f, ok := n.(*ast.SelectorExpr); ok{
		if x, ok := f.X.(*ast.Ident); ok{
			if v, ok := si.dbCallPara[x.Name]; ok{
				return v, f.Sel.Name, true
			}
		}
	}
	return "", "", false
}

func (si *Analyzer) checkDbCall(node *ast.CallExpr, iType string, fName string){
	panic(1)
}

func (si *Analyzer) Visit(n ast.Node) ast.Visitor {
	if n == nil{
		si.upDateStateAfterPop()
		//fmt.Printf("pop len is %d\n", si.caseStack.Len())
		return nil
	} else {
		si.caseStack.PushBack(n)
		//fmt.Printf("push len is %d\n", si.caseStack.Len())
		switch node:= n.(type){
			case *ast.Field:
				if si.isFunctionParaName(){
					if len(node.Names) > 0{
						//fmt.Printf("%s %s\n", node.Names[0].Name, getParaType(*node))
						si.parameters = append(si.parameters, 
							functionPara{pName:node.Names[0].Name, pType:getParaType(*node)})
					}
					si.AddDbCallPara(node.Names[0].Name, getParaType(*node))
				}
			case *ast.FuncDecl:
				if	si.state == StateMentAnalysis_START{
					si.curFunName = node.Name.Name
					si.ChangeState(StateMentAnalysis_FUNCTION)
				}
			case *ast.BlockStmt:{
				if	si.state == StateMentAnalysis_FUNCTION{
					si.ChangeState(StateMentAnalysis_FUNCTION_BODY)
				}
			}
			case *ast.CallExpr:{
				//fmt.Printf("call expr %d\n", si.state )
				if si.state == StateMentAnalysis_FUNCTION_BODY{
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
					}
					
					if iType, fName, ok := si.isDbInterfaceCall(n); ok{
						si.checkDbCall(node, iType, fName)
					}
					
				}
			}
			case *ast.AssignStmt:{
				if si.state == StateMentAnalysis_FUNCTION_BODY{
					// del right
					dbInput := si.getDbInputFromRhs(node.Rhs[0])
					
					if dbInput.format != ""{
						if v, ok := node.Lhs[0].(*ast.Ident); ok{
							si.allPossibleInput[v.Name] = dbInput
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

func main(){
	flag.Parse()
	si  := &Analyzer{
		logger:	log.New(os.Stderr, "[sqlinj]", log.LstdFlags),
		caseStack:   list.New(),
		parameters:       make([]functionPara,1),
		state:       StateMentAnalysis_START,
		allPossibleInput: make(map[string]*DbInput),
	}
	si.CheckDir(*checkDir)
	//fmt.Println(getPackagePaths(*checkDir))
}
