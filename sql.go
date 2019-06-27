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
	result := []string{}
	return result, nil
}

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
	logger      *log.Logger
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

func (si *Analyzer) check(pkg *packages.Package) {
	//si.logger.Println("Checking package:", pkg.Name)
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
		BuildFlags: flags,
		Tests:      false,
	}
}

func (si *Analyzer) Process(buildTags []string, packagePaths ...string) error {
	config := si.pkgConfig(buildTags)
	for _, pkgPath := range packagePaths {
		pkgs, err := si.load(pkgPath, config)
		if err != nil {
			//si.AppendError(pkgPath, err)
			fmt.Println(pkgPath, ":", err)
		}
		for _, pkg := range pkgs {
			if pkg.Name != "" {
				si.check(pkg)
			}
		}
	}
	//sortErrors(si.errors)
	return nil
}

func main(){
}
