module RosiJS.Compiler where
import Data.List                      (intercalate)
import Language.JavaScript.Parser.AST
import Syntax
import qualified Debug.Trace as T

compileDecls :: [Decl] -> JSAST
compileDecls decls = JSAstProgram (map compileDecl tmDecls) JSAnnotSpace
  where
  tmDecls = [decl | decl@(TmDecl qn _ tm) <- decls]

fromQName :: QName -> String
fromQName = intercalate "_" . reverse

compileDecl :: Decl -> JSStatement
compileDecl (TmDecl qn _ tm) = JSConstant
  JSAnnotSpace
  (JSLOne
    (JSAssignExpression (JSIdentifier JSAnnotSpace (fromQName qn)) (JSAssign JSAnnotSpace) (compileExpr tm)))
  (JSSemi JSAnnotSpace)
compileDecl _ = error "can only compile term declarations."

compileExpr :: Term -> JSExpression
compileExpr arg | T.trace ("compileExpr: " ++ show arg) False = undefined
compileExpr (EVar n qname)              = JSIdentifier JSAnnotSpace (intercalate "_" (reverse qname))
compileExpr (ELam x ty tm)              = JSArrowExpression (JSUnparenthesizedArrowParameter (JSIdentName JSAnnotSpace x)) JSAnnotSpace (compileStatement tm)
compileExpr (EApp ft xt)                = JSCallExpression (compileExpr ft) JSAnnotSpace (JSLOne (compileExpr xt)) JSAnnotSpace

compileExpr (ETyLam s k tm )            = error "can't compile tylam to JS"
compileExpr (EPrLam p tm)               = compileExpr tm
compileExpr (EInst tm insts)            = compileExpr tm

compileExpr (ESing (TLab s))            = JSStringLiteral JSAnnotSpace s
compileExpr (ESing ty)                  = error "can't compile singleton that is not a label"
compileExpr (ELabel (Just Pi) lt xt)    = JSObjectLiteral JSAnnotSpace (JSCTLNone (JSLOne (JSPropertyNameandValue (compileLabelIdent lt) JSAnnotSpace [compileExpr xt] ))) JSAnnotSpace
compileExpr (ELabel (Just Sigma) lt xt) = undefined
compileExpr (ELabel Nothing lt xt)      = JSObjectLiteral JSAnnotSpace (JSCTLNone (JSLOne (JSPropertyNameandValue (compileLabelIdent lt) JSAnnotSpace [compileExpr xt] ))) JSAnnotSpace
compileExpr (EUnlabel tc xt lt)         = undefined

compileExpr (EConst c)                  = undefined

compileExpr (ELet x vt et)              = undefined
compileExpr (ECast tm evid)             = undefined
compileExpr (ETyped tm ty)              = undefined

compileExpr (EStringLit s)              = JSStringLiteral JSAnnotSpace s
compileExpr (EHole s)                   = undefined

compileLabelIdent :: Term -> JSPropertyName
compileLabelIdent = undefined

-- compileExpr (EInfix _)        = error "desugar infix before passing to js compiler"

compileStatement :: Term -> JSStatement
compileStatement arg | T.trace ("compileStatment: " ++ show arg) False = undefined
compileStatement var@(EVar n qname)      = JSExpressionStatement (compileExpr var) (JSSemi JSAnnotSpace)
compileStatement (ELam x ty tm)      = undefined
compileStatement (EApp ft xt)        = undefined

compileStatement (ETyLam s k tm )    = undefined
compileStatement (EPrLam p tm)       = undefined
compileStatement (EInst tm insts)    = undefined

compileStatement (ESing ty)          = undefined
compileStatement (ELabel tc lt xt)   = undefined
compileStatement (EUnlabel tc xt lt) = undefined

compileStatement (EConst c)          = undefined

compileStatement (ELet x vt et)      = undefined
compileStatement (ECast tm evid)     = undefined
compileStatement (ETyped tm ty)      = undefined

compileStatement (EStringLit s)      = undefined
compileStatement (EHole s)           = undefined

-- compileExpr (EInfix _)        = error "desugar infix before passing to js compiler"
