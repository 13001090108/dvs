package softtest.depchain.c;

import java.util.List;

import softtest.ast.c.ASTANDExpression;
import softtest.ast.c.ASTAbstractDeclarator;
import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTAssignmentOperator;
import softtest.ast.c.ASTCastExpression;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTConditionalExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTConstantExpression;
import softtest.ast.c.ASTDeclaration;
import softtest.ast.c.ASTDeclarationList;
import softtest.ast.c.ASTDeclarationSpecifiers;
import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTDirectAbstractDeclarator;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTEnumSpecifier;
import softtest.ast.c.ASTEnumerator;
import softtest.ast.c.ASTEnumeratorList;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTExclusiveORExpression;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTExpressionStatement;
import softtest.ast.c.ASTExternalDeclaration;
import softtest.ast.c.ASTFieldId;
import softtest.ast.c.ASTFunctionDeclaration;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTIdentifierList;
import softtest.ast.c.ASTInclusiveORExpression;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTInitDeclaratorList;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTInitializerList;
import softtest.ast.c.ASTIterationStatement;
import softtest.ast.c.ASTJumpStatement;
import softtest.ast.c.ASTLabelDeclaration;
import softtest.ast.c.ASTLabelDeclarationList;
import softtest.ast.c.ASTLabelDeclarator;
import softtest.ast.c.ASTLabelDeclaratorList;
import softtest.ast.c.ASTLabelType;
import softtest.ast.c.ASTLabeledStatement;
import softtest.ast.c.ASTLogicalANDExpression;
import softtest.ast.c.ASTLogicalORExpression;
import softtest.ast.c.ASTMultiplicativeExpression;
import softtest.ast.c.ASTNestedFunctionDeclaration;
import softtest.ast.c.ASTNestedFunctionDefinition;
import softtest.ast.c.ASTPRAGMA;
import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.ASTParameterTypeList;
import softtest.ast.c.ASTPointer;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTRelationalExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTShiftExpression;
import softtest.ast.c.ASTSpecifierQualifierList;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.ASTStorageClassSpecifier;
import softtest.ast.c.ASTStructDeclaration;
import softtest.ast.c.ASTStructDeclarationList;
import softtest.ast.c.ASTStructDeclarator;
import softtest.ast.c.ASTStructDeclaratorList;
import softtest.ast.c.ASTStructOrUnion;
import softtest.ast.c.ASTStructOrUnionSpecifier;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.ASTTypeName;
import softtest.ast.c.ASTTypeQualifier;
import softtest.ast.c.ASTTypeQualifierList;
import softtest.ast.c.ASTTypeSpecifier;
import softtest.ast.c.ASTTypedefName;
import softtest.ast.c.ASTTypeofDeclarationSpecifier;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTUnaryOperator;
import softtest.ast.c.CParserVisitor;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;

public class ExternalInputSourceASTVisitor implements CParserVisitor {

	@Override
	public Object visit(SimpleNode node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTTranslationUnit node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTExternalDeclaration node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTFunctionDeclaration node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTFunctionDefinition node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTDeclaration node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTDeclarationList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTNestedFunctionDeclaration node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTNestedFunctionDefinition node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTLabelDeclarationList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTLabelDeclaration node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTLabelDeclaratorList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTLabelDeclarator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTLabelType node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTDeclarationSpecifiers node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTTypeofDeclarationSpecifier node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStorageClassSpecifier node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTTypeSpecifier node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTTypeQualifier node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStructOrUnionSpecifier node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStructOrUnion node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStructDeclarationList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTInitDeclaratorList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTInitDeclarator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStructDeclaration node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTSpecifierQualifierList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStructDeclaratorList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStructDeclarator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTEnumSpecifier node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTEnumeratorList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTEnumerator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTDeclarator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTDirectDeclarator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTPointer node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTTypeQualifierList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTParameterTypeList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTParameterList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTParameterDeclaration node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTIdentifierList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTInitializer node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTInitializerList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTTypeName node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTAbstractDeclarator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTDirectAbstractDeclarator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTTypedefName node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStatement node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTLabeledStatement node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTExpressionStatement node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTCompoundStatement node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTStatementList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTSelectionStatement node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTIterationStatement node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTJumpStatement node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTAssignmentExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTAssignmentOperator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTConditionalExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTConstantExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTLogicalORExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTLogicalANDExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTInclusiveORExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTExclusiveORExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTANDExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTEqualityExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTRelationalExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTShiftExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTAdditiveExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTMultiplicativeExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTCastExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTUnaryExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTUnaryOperator node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTPostfixExpression node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTPrimaryExpression node, Object data) {
		List<ExternalInputSource> list = (List<ExternalInputSource>) data;
    	String[] defFuncs = new String[]{"scanf","gets","strcpy","strdup","free","malloc","calloc","realloc","gets","getc","getchar","fopen"};

		if (node.isLeaf() && node.isMethod()) {
			String image = node.getImage();
			for (String defFunc : defFuncs) {
				if (image.equals(defFunc)) {
					ASTAssignmentExpression assign = (ASTAssignmentExpression) node.getFirstParentOfType(ASTAssignmentExpression.class);
					while (!(assign.jjtGetNumChildren() == 3 && assign.jjtGetChild(1) instanceof ASTAssignmentOperator)) {
						assign = (ASTAssignmentExpression) node.getFirstParentOfType(ASTAssignmentExpression.class);
					}
					SimpleNode left = (SimpleNode) assign.jjtGetChild(0);
					List<Node> leftvars = left.findChildrenOfType(ASTPrimaryExpression.class);
					for (Node n : leftvars) {
						SimpleNode s = (SimpleNode) n;
						if (s.isLeaf()) {
		    				ExternalInputSource e = new ExternalInputSource();
		    				e.setFileName(s.getFileName());
		    				e.setVarName(s.getImage());
		    				ASTFunctionDefinition f = (ASTFunctionDefinition) s.getFirstParentOfType(ASTFunctionDefinition.class);
		    				e.setFuncName(f.getImage());
		    				e.setLine(s.getBeginLine());
							list.add(e);
						}
					}
				}
			}
		}
		return null;
	}

	@Override
	public Object visit(ASTArgumentExpressionList node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTConstant node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTFieldId node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visit(ASTPRAGMA node, Object data) {
		// TODO Auto-generated method stub
		return null;
	}

}
