import sys
import xml.etree.ElementTree as ET
from xml.dom import minidom
from lark import Lark, Visitor, Transformer, exceptions, Tree, Token
import re

liveVersion = False
enableUserInput = liveVersion
printTree = liveVersion
# parameters and class methods act like part of variables, including two class constructors, classMethods
specialMethods: set = {"run"}
builtinIdentifiers: set = {"class", "self", "super", "nil", "true", "false"}
builtinClasses: set = {"Object", "Nil", "True", "False", "Integer", "String", "Block"}
availableIdentifiers: set = {"self", "super", "nil", "true", "false"}
availableIdentifierObjects: set = {"nil", "true", "false"}
reservedKeywords: set = builtinIdentifiers | builtinClasses
# instance methods (callable on class instance), class methods (callable on both class instance and class)
builtinConstructors: set = {"new"}
builtinWParamConstructors: set = {"from"}
# Object Class
methodsObject: set = {"asString", "isNumber", "isString", "isBlock", "isNil"}
# Subclasses of Object, ones with : are multi-parameter
classMethodStringObject: set = {"read"}
methodsWParamBlockObject: set = {"whileTrue, value"}  # value based on block arguments
methodsNilObject: set = {"asString"}
methodsWParamNilObject: set = {"identicalTo", "equalTo"}
methodsIntegerObject: set = {"asString, asInteger"}
methodsWParamIntegerObject: set = {"equalTo", "greaterThan", "plus", "minus", "multiplyBy", "divBy", "timesRepeat"}
methodsStringObject: set = {"print", "asString", "asInteger", "read"}
methodsWParamStringObject: set = {"equalTo", "concatenateWith", "startsWith:endsBefore"}
methodsTrueObjectFalseObject: set = {"not"}
methodsWParamFalseObjectAndTrueObject: set = {"and", "or", "ifTrue, ifFalse"}

# children[n] equivalent to children[0].value if ending node, because of __str__ method
methodsClass: dict = {
    'Nil': methodsNilObject,
    'Integer': methodsIntegerObject,
    'String': methodsStringObject,
    'True': methodsTrueObjectFalseObject,
    'False': methodsTrueObjectFalseObject, }
methodsWParamClass: dict = {
    'Nil': methodsWParamNilObject,
    'Integer': methodsWParamIntegerObject,
    'String': methodsWParamStringObject,
    'True': methodsWParamFalseObjectAndTrueObject,
    'False': methodsWParamFalseObjectAndTrueObject, }

builtinMethods: set = builtinConstructors | methodsObject | methodsNilObject | methodsIntegerObject | methodsStringObject | methodsTrueObjectFalseObject
builtinMethodsWParams: set = builtinWParamConstructors | methodsWParamBlockObject | methodsWParamNilObject | methodsWParamIntegerObject | methodsWParamStringObject | methodsWParamFalseObjectAndTrueObject
inputTest = """
 class Main : Object {run [|]}
            class Main2 : Object {run [|]}
"""
# A:(B C)* creates flat list with B, C
# A: D*, D: B C create individual trees
grammar = ''' 
%import common.WS
%ignore WS
%import common.NEWLINE
%ignore NEWLINE
%ignore /"[^"]*"/

program: class*                             
class: "class" cid ":" cid "{" method "}"   -> class_def
method: ( selector block )*                 -> method_def
selector: id | selector_tail         
selector_tail: ( id ":" )+

block: "[" block_par "|" block_stat "]"
block_par: ( ":" id )*
block_stat: ( id ":=" expr "." )*

expr: expr_base expr_tail
expr_tail: id | expr_sel
expr_sel: ( id ":" expr_base )*
expr_base: int | str | id | cid | block | "(" expr ")"

cid: /[A-Z][A-Za-z0-9_]*/
id: /[a-z_][A-Za-z0-9_]*/
int: /[+-]?[0-9]+(?![a-zA-Z_])/
str: /'([^'\\]|\\['\\n])*'/
'''

class ReservedKeywordsUse(Visitor):
    def block_stat(self, tree):
        i = 0
        while i < len(tree.children):
            if len(tree.children[i].children) > 0:
                firstIdName = tree.children[i].children[0].value
                if firstIdName in reservedKeywords | builtinConstructors | builtinWParamConstructors:
                    print(f"Syntactic Error: Reserved keyword in assignment", file=sys.stderr)
                    sys.exit(22)
            i += 2

    def block_par(self, tree):
        for child in tree.children:
            paramName = child.children[0].value
            if paramName in reservedKeywords | builtinConstructors | builtinWParamConstructors:
                print(f"Syntactic Error: Reserved keyword in parameter", file=sys.stderr)
                sys.exit(22)

    def expr_sel(self, tree):
        for i in range(0, len(tree.children), 2):
            idPart = tree.children[i].children[0].value
            basePart = tree.children[i + 1].children[0]

            if idPart in reservedKeywords | builtinConstructors:
                print(f"Syntactic Error: Reserved keyword in selector id ", file=sys.stderr)
                sys.exit(22)
            if basePart.data not in {'block', 'expr'}:
                basePartFinal = basePart.children[0].value
                if basePartFinal in reservedKeywords | builtinConstructors | builtinWParamConstructors:
                    print(f"Syntactic Error: Reserved keyword in selector base", file=sys.stderr)
                    sys.exit(22)

    def expr_tail(self, tree):
        tailPart = tree.children[0]
        if tailPart.data == "id":
            tailId = tailPart.children[0].value
            if tailId in reservedKeywords | builtinWParamConstructors:
                print(f"Syntactic Error: Reserved keyword in expression tale", file=sys.stderr)
                sys.exit(22)

    def selector(self, tree):
        selectorPart = tree.children[0]
        if selectorPart.data == "id":
            selectorId = selectorPart.children[0].value
            if selectorId in reservedKeywords | builtinConstructors | builtinWParamConstructors:
                print(f"Syntactic Error: Reserved keyword in method selector", file=sys.stderr)
                sys.exit(22)

        if selectorPart.data == "selector_tail":
            for child in selectorPart.children:
                selectorId = child.children[0].value
                if selectorId in reservedKeywords | builtinConstructors | builtinWParamConstructors:
                    print(f"Syntactic Error: Reserved keyword in method selector tail", file=sys.stderr)
                    sys.exit(22)
class ClassMainRun(Visitor):  # check Main with its first id being instance method run
    def __init__(self):
        self.insideMain = False
        self.runInMain = False
        self.methodCount = 0

    def class_def(self, tree):
        cidTree = tree.children[0]
        className = cidTree.children[0].value
        if className == "Main":
            self.insideMain = True

    def method_def(self, tree):
        if len(tree.children) > 0:
            selectorTree = tree.children[0]
            selectorTreeChild = selectorTree.children[0]
            if selectorTreeChild.data == "id":
                firstIdName = selectorTreeChild.children[0].value
                if self.insideMain and firstIdName == "run":
                    self.runInMain = True

    def runInMainConfirm(self):
        if not self.runInMain:
            print(f"Semantic Error Missing 'Main' class with 'run' instance method", file=sys.stderr)
            sys.exit(31)
class ArityBlockSelector(Visitor):
    def method_def(self, tree):
        selectorTailIdCount = 0
        blockParCount = 0
        for child in tree.children:
            if child.data == "selector":
                if child.children[0].data == "selector_tail":
                    selectorTailIdTree = child.children[0]
                    selectorTailIdCount = len(selectorTailIdTree.children)

            if child.data == "block":
                blockParTree = child.children[0]
                blockParCount = len(blockParTree.children)
        if selectorTailIdCount != blockParCount:
            print(f"Semantic Error: Incorrect arity in method definition", file=sys.stderr)
            sys.exit(33)
class CollisionVariable(Visitor):
    def block(self, tree):
        blockParametersSaved = set()
        blockDefinedVariablesSaved = set()
        blockParTree = tree.children[0]
        blockParams = blockParTree.children

        for param in blockParams:
            paramName = param.children[0].value
            if paramName in blockParametersSaved:
                print("Semantic Error: Duplicate parameter in block", file=sys.stderr)
                sys.exit(35)
            blockParametersSaved.add(paramName)

        blockStatTree = tree.children[1]
        for statement in blockStatTree.children:
            if statement.data == "id":
                variableName = statement.children[0].value
                blockDefinedVariablesSaved.add(variableName)

        if blockParametersSaved & blockDefinedVariablesSaved:  # intersection
            print(f"Semantic Error: Variable collision in block", file=sys.stderr)
            sys.exit(34)

firstDefinedPassthrough = True
definedClasses = set()
definedMethods = set()  # callable before declaration
definedMethodsWParams = set()  # callable before declaration
classesSubclasses = [
    ("Object", []),
    ("Nil", []),
    ("True", []),
    ("False", []),
    ("Integer", []),
    ("String", []),
    ("Block", [])
]

# 1st passthrough to save classes and methods
class DefinedElementsAndTypes(Visitor):  # check defined variables, parameters, classes and class methods
    # first interpretable expression base apart from 'expr' defines the type of id assigned id : == expr_base expr_tail
    # self refers to current class, super to the parent of current class
    # variables visible only within block exclusively, methods usable outside
    def __init__(self):
        self.currentClassType = None  # string
        self.currentIdType = None  # string or None
        self.currentIdIndex = 0  # helper for indexes of multi-level methods
        self.classesSaved = set()
        self.methodsSaved = set()
        self.methodsWParamsSaved = set()
        self.definedVariables = set()  # specific for block

    def addToClassList(self, className, parentClass):
        for classInfo in classesSubclasses:
            if classInfo[0] == parentClass:
                classInfo[1].append(className)
                return

    def findClassList(self, className):
        for classInfo in classesSubclasses:
            if className in classInfo[1]:
                return classInfo[1]
        return None

    def findParentClass(self, className):
        classList = self.findClassList(className)
        index = classList.index(className)
        if index > 0:
            parentClass = classList[index - 1]
            return parentClass
        return classList[0]

    # Class
    def class_def(self, tree):
        className = tree.children[0].children[0]
        classParentName = tree.children[1].children[0]
        self.currentClassType = classParentName
        self.addToClassList(className, classParentName)

        if firstDefinedPassthrough:
            if className in self.classesSaved:
                print(f"Semantic Error: Class redefinition '{className}'", file=sys.stderr)
                sys.exit(35)
            definedClasses.add(className)
            self.classesSaved.add(className)
        elif not firstDefinedPassthrough:
            if classParentName not in definedClasses | builtinClasses:
                print(f"Semantic Error: Undefined class parent used{classParentName}", file=sys.stderr)
                sys.exit(32)


    # Block
    def block(self, tree):
            self.definedVariables = set()  # reset defined variables
            for child in tree.children:
                if child.data == "block_par":
                    for param in child.children:
                        paramId = param.children[0].value
                        self.definedVariables.add((paramId, None))

            for child in tree.children:
                if child.data == "block_stat":
                    for statement in child.children:
                        if statement.data == "id":
                            if len(statement.children) > 0:
                                varId = statement.children[0].value
                                self.currentIdType = None  # reset stat
                                self.definedVariables.add((varId, self.currentIdType))  # adding tuple
                        if statement.data == "expr":
                            self.exprCheck(statement)

    def idCheckHelper(self, element, type):
        idName = element.children[0].value
        methodWParams = set(part for var in definedMethodsWParams for part in var.split(':'))
        builtinMethodWParams = set(part for var in builtinMethodsWParams for part in var.split(':'))
        if type == 'selector':
            if idName not in (methodWParams | builtinMethodWParams | builtinConstructors | availableIdentifiers):
                print(f"Semantic Error: Undefined method variable in expression selector '{idName}'",file=sys.stderr)
                sys.exit(32)
        elif type == 'tail':
            if idName not in (
                    {var[0] for var in self.definedVariables} | availableIdentifiers | builtinConstructors):
                print(f"Semantic Error: Undefined method variable in expression tail '{idName}'",
                      file=sys.stderr)
                sys.exit(32)
        elif idName not in {var[0] for var in self.definedVariables} | availableIdentifiers | builtinConstructors:
            print(f"Semantic Error: Undefined variable in expression '{idName}'", file=sys.stderr)
            sys.exit(32)
        elif idName in availableIdentifierObjects:
            if idName == 'true':
                self.currentIdType = 'True'
            elif idName == 'false':
                self.currentIdType = 'False'
            elif idName == 'nil':
                self.currentIdType = 'Nil'
        elif idName == 'self':
            self.currentIdType = self.currentClassType
        elif idName == 'super':
            self.currentIdType = self.findParentClass(self.currentClassType)

    def exprCheck(self, tree):
        exprBase = tree.children[0].children[0]
        self.exprBaseCheck(exprBase)
        exprTail = tree.children[1].children[0]
        self.exprTailCheck(exprTail)

    def exprBaseCheck(self, element):
        if element.data == 'int':
            if self.currentIdType is None:
                self.currentIdType = 'Integer'
        elif element.data == 'str':
            if self.currentIdType is None:
                self.currentIdType = 'String'
        elif element.data == 'id':
            self.idCheckHelper(element, 'base')
        elif element.data == 'cid':
            cidName = element.children[0].value
            if cidName not in definedClasses | builtinClasses:
                print(f"Semantic Error: Undefined class '{cidName}'", file=sys.stderr)
                sys.exit(32)
            self.currentIdType = cidName
        elif element.data == 'block':
            self.currentIdType = 'Block'
            self.block(element)
        elif element.data == 'expr':
            self.exprCheck(element)

    def exprTailCheck(self, tree):
        if tree.data == "id":  # method without parameters
            self.idCheckHelper(tree, 'tail')
        elif tree.data == "expr_sel":
            self.exprSelCheck(tree)  # method with parameter(s)

    def exprSelCheck(self, tree):
        for index, element in enumerate(tree.children):
            if element.data == "id":
                self.idCheckHelper(element, 'selector')
            elif element.data == "expr_base":
                exprBase = element.children[0]
                self.exprBaseCheck(exprBase)

    # method
    def method_def(self, tree):
        if firstDefinedPassthrough:
            for element in tree.children:
                if element.data == "selector":
                    selectorPart = element.children[0]
                    if selectorPart.data == "id":
                        methodName = selectorPart.children[0].value
                        if methodName not in specialMethods:
                            if methodName in self.methodsSaved | builtinMethods:
                                print(f"Semantic Error: method redefinition {methodName}", file=sys.stderr)
                                sys.exit(35)
                            definedMethods.add(methodName)
                            self.methodsSaved.add(methodName)
                    elif selectorPart.data == "selector_tail":
                        selectorTail = element.children[0].children
                        if len(selectorTail) == 1:
                            methodName = selectorTail[0].children[0].value
                            if methodName in self.methodsSaved | builtinMethods:
                                print(f"Semantic Error: method redefinition {methodName}", file=sys.stderr)
                                sys.exit(35)
                            definedMethodsWParams.add(methodName)
                            self.methodsSaved.add(methodName)
                        elif len(selectorTail) > 1:
                            methodIds = [methodId.children[0].value for methodId in selectorTail]
                            methodNameJoined = ":".join(methodIds)
                            if methodNameJoined in self.methodsWParamsSaved | builtinMethods:
                                print(f"Semantic Error: method redefinition {methodNameJoined}", file=sys.stderr)
                                sys.exit(35)
                            definedMethodsWParams.add(methodNameJoined)
                            self.methodsWParamsSaved.add(methodNameJoined)

arguments = sys.argv[1:]  # take from 1st index, 0th being script directory
argumentsLength = len(arguments)

if (argumentsLength == 1 and arguments[0] == "--help") or (argumentsLength == 1 and arguments[0] == "-h"):
    print("Use Interpreter script by passing code to standard input")
    sys.exit(0)  # return with 0
elif argumentsLength >= 1:
    print("use '--help' as argument to show help message", file=sys.stderr)
    sys.exit(10)  # return with ERROR 10

if enableUserInput:
    inputCode = sys.stdin.read()
else:
    inputCode = inputTest

classLiterals: set = {"Integer", "String", "Nil", "True", "False"}
class CodeTransformer(Transformer):
    def __init__(self):
        super().__init__()

    def getFirstComment(self):
        blockComment = re.search(r'"([^"]*)"', inputCode)
        if blockComment:
            comment = blockComment.group(1)
            return comment
        else:
            return None

    def program(self, items):
        programElem = ET.Element('program', language='SOL25')

        comment = self.getFirstComment()
        if comment:
            programElem.set('description', comment)

        for item in items:
            programElem.append(item)

        return programElem

    def class_def(self, items):
        className = items[0]
        parentName = items[1]
        methods = items[2]
        classElem = ET.Element('class', name=className, parent=parentName)

        if isinstance(methods, list):
            for method in methods:
                if method.attrib.get('selector') or len(method) > 0:
                    classElem.append(method)
        else:
            if methods.attrib.get('selector') or len(methods) > 0:
                classElem.append(methods)
        return classElem

    def selector(self, items):
        return items[0]

    def selector_tail(self, items):
        return items[0]

    def method_def(self, items):
        methodElem = ET.Element('method')
        for i in range(0, len(items), 2):
            methodElem.set('selector', items[i])
            blockElem = items[i + 1]
            methodElem.append(blockElem)
        return methodElem

    def block(self, items):
        blockElem = ET.Element('block', arity=str(len(items[0])))
        if items[0]:
            for paramElem in items[0]:
                blockElem.append(paramElem)

        if len(items) > 1:
            for stat in items[1]:
                blockElem.append(stat)

        return blockElem

    def helperDetermineExp(self, item):
        exprElem = ET.Element('expr')

        if not item or (isinstance(item, str) and item.strip() == ""):
            return item

        if isinstance(item, str):
            if item.type == "id":
                if item == "true":
                    literalElem = ET.Element('literal')
                    literalElem.set('class', 'True')
                    literalElem.set('value', item)
                    exprElem.append(literalElem)
                elif item == "false":
                    literalElem = ET.Element('literal')
                    literalElem.set('class', 'False')
                    literalElem.set('value', item)
                    exprElem.append(literalElem)
                elif item == "nil":
                    literalElem = ET.Element('literal')
                    literalElem.set('class', 'Nil')
                    literalElem.set('value', item)
                    exprElem.append(literalElem)
                else:
                    varElem = ET.Element('var', name=item)
                    exprElem.append(varElem)
            elif item.type == "int":
                literalElem = ET.Element('literal')
                literalElem.set('class', 'Integer')
                literalElem.set('value', item)
                exprElem.append(literalElem)
            elif item.type == "str":
                literalElem = ET.Element('literal')
                literalElem.set('class', 'String')
                literalElem.set('value', item[1:-1])
                exprElem.append(literalElem)
            elif item.type == "cid":
                if item in classLiterals:
                    literalElem = ET.Element('literal')
                    literalElem.set('class', "class")
                    literalElem.set('value', item)
                    exprElem.append(literalElem)
                else:
                    varElem = ET.Element('var', name=item)
                    exprElem.append(varElem)
        else:
            exprElem.append(item)
        return exprElem

    def expr(self, items):
        baseItem = items[0]
        tailItem = items[1]

        exprElem = self.helperDetermineExp(baseItem)
        if not tailItem:
            return exprElem

        sendElem = ET.Element('send')
        sendElem.append(exprElem)

        selParts = []
        argIndex = 0

        if isinstance(tailItem, str):
            selParts.append(tailItem)
        elif isinstance(tailItem, list):
            i = 0
            while i < len(tailItem):
                sel = tailItem[i]
                selParts.append(f"{sel}:")

                if i + 1 < len(tailItem):
                    arg = tailItem[i + 1]
                    argIndex += 1
                    argExpElem = self.helperDetermineExp(arg)
                    argElem = ET.Element('arg', order=str(argIndex))
                    argElem.append(argExpElem)
                    sendElem.append(argElem)
                i += 2

        selectorStr = "".join(selParts)
        sendElem.set('selector', selectorStr)
        outExprElem = ET.Element('expr')
        outExprElem.append(sendElem)

        return outExprElem

    def expr_base(self, items):
        if len(items) == 1:
            return items[0]
        return items

    def expr_tail(self, items):
        return items[0]

    def expr_sel(self, items):
        return items

    def block_par(self, items):
        parameters = []
        for i, param in enumerate(items, start=1):
            paramElem = ET.Element('parameter', name=param, order=str(i))
            parameters.append(paramElem)

        return parameters

    def block_stat(self, items):
        assigns = []
        order = 1

        for i in range(0, len(items), 2):
            varName = items[i]
            exprElem = items[i + 1]

            assignElem = ET.Element('assign', order=str(order))
            varElem = ET.Element('var', name=varName)
            assignElem.append(varElem)
            assignElem.append(exprElem)
            assigns.append(assignElem)
            order += 1
        return assigns

    def id(self, token):
        token[0].type = "id"
        return token[0]

    def cid(self, token):
        token[0].type = "cid"  # access with token 0
        return token[0]

    def int(self, token):
        token[0].type = "int"
        return token[0]

    def str(self, token):
        token[0].type = "str"
        return token[0]

parser = Lark(grammar, start="program", parser="lalr", lexer="contextual")
syntacticReservedKeywordsUse = ReservedKeywordsUse()
semanticClassMainRun = ClassMainRun()
semanticArityBlockSelector = ArityBlockSelector()
semanticCollisionVariable = CollisionVariable()
semanticDefinedElements = DefinedElementsAndTypes()
xmlTransformer = CodeTransformer()

# order of exceptions matters, first invoked is activated
try:
    finalTree = parser.parse(inputCode)

    syntacticReservedKeywordsUse.visit_topdown(finalTree)  # Error 22
    semanticClassMainRun.visit_topdown(finalTree)  # Error 31
    semanticClassMainRun.runInMainConfirm()
    semanticDefinedElements.visit_topdown(finalTree)
    firstDefinedPassthrough = False
    semanticDefinedElements.visit_topdown(finalTree)  # Error 32
    semanticArityBlockSelector.visit_topdown(finalTree)  # Error 33
    semanticCollisionVariable.visit_topdown(finalTree)  # Error 34, 35

    xmlRoot = xmlTransformer.transform(finalTree)
    xmlString = ET.tostring(xmlRoot, encoding="utf-8").decode("utf-8")
    xmlHeader = '<?xml version="1.0" encoding="UTF-8"?>'
    finalXML = xmlHeader + xmlString

    domXML = minidom.parseString(finalXML)
    prettyXML = domXML.toprettyxml(indent="  ", encoding="utf-8").decode("utf-8")
    if printTree: sys.stdout.write(prettyXML)


except exceptions.UnexpectedCharacters as e:
    print(f"UnexpectedCharacters: {e}", file=sys.stderr)
    sys.exit(21)
except exceptions.UnexpectedToken as e:
    print(f"UnexpectedToken: {e}", file=sys.stderr)
    sys.exit(22)
