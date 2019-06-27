package main
import (
	"flag"
	"fmt"
	"container/list"
	"go/ast"
)

var checkDir = flag.String("dir", "", "sql injection check dir")

type functionPara struct{
	pName string
	pType string
}

type StateMentAnalysis int 
const (
	_ StateMentAnalysis = iota
	StateMentAnalysis_START
	StateMentAnalysis_FUNCTION
	StateMentAnalysis_FUNCTION_BODY
)

type Analyzer struct {
	ignoreNosec bool
	
	caseStack   *list.List
	parameters  [] functionPara
	curParaName   string
	curParaType   string
	state       StateMentAnalysis
	curFunName    string
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
		case *ast.CallExpr:
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
			}

		}

		
		return si
	}
}

func main(){
}
