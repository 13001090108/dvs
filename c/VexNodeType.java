package softtest.depchain.c;

import java.util.List;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;

/**
 *
 *�Կ������ڵ����ͽ����ж�
 *type == 0 ������ͼ��ڽڵ�
 *type == 1 ֻ�к��� f()����f(c)
 *type == 2 �ж������� �� ���� int c = m + f();
 *type == 3 �ж�������(����������δ��ֵ) , ����int c;
 *type == 4 �޶������� �� ���� c = m + a;
 *type == 5 ������ͼ���ڽڵ�
 *type == 6 �⺯��
 *type == 7 ������� ����c ++
 *type == 8 �����ݽڵ�
 */
public  enum VexNodeType {
	/**
	 * ������ͼ��ڽڵ�",0
	 */
	TYPE_0("������ͼ��ڽڵ�",0),
	/**"ֻ�к��� f()����f(c)",1 */
	TYPE_1("ֻ�к��� f()����f(c)",1),
	/**"�ж������� ", 2 */
	TYPE_2("�ж�������",2),
	/***    "�ж�������(����������δ��ֵ)",3   */
	TYPE_3("�ж�������(����������δ��ֵ)",3),
	/** "�޶�������",4 */
	TYPE_4("�޶�������",4),
	/**"������ͼ���ڽڵ�",5*/
	TYPE_5("������ͼ���ڽڵ�",5),
	/**"�⺯��",6**/
	TYPE_6("�⺯��",6),
	/***"������������������Լ�����",7*/
	TYPE_7("�������,",7),
	/**"�����ݽڵ�",8**/
	TYPE_8("�����ݽڵ�",8)
	;
	
	private String name;
	private int index;
	
	private VexNodeType(String name, int index) {  
        this.name = name;  
        this.index = index;  
    }
	VexNodeType() 	{
		
	}
//	public static String getName(VexNodeType type) {
//		return type.name;
//	}
	@Override
	 public String toString() {  
	        return this.index+"_"+this.name;  
	 }
	
	/**
	 * �жϴ���������ڵ�����
	 * @param vexNode
	 * @param list_outsource
	 * @return
	 */
	public static String getVexNodeType(VexNode vexNode , List<String> list_outsource  ) {
		SimpleNode treeNode = vexNode.getTreenode();
		String type =VexNodeType.TYPE_8.name();
		if(vexNode.getOutedges().isEmpty()) {
			type = VexNodeType.TYPE_6.name();
		}
		else if(vexNode.getInedges().isEmpty()) {
			type = VexNodeType.TYPE_0.name();
		}
		else {
			if(treeNode.toString().equals("Declaration")) {
				ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) treeNode.getFirstChildOfType(ASTInitDeclarator.class);
				if(astInitDeclarator.jjtGetNumChildren() == 1) {
					type = VexNodeType.TYPE_3.name();
				}
				else if(astInitDeclarator.jjtGetNumChildren() == 2) {
					type = VexNodeType.TYPE_2.name();
				}
				
			}
			else if(treeNode.toString().equals("ExpressionStatement")) {
				ASTAssignmentExpression assignmentExpression = (ASTAssignmentExpression) treeNode.getFirstChildOfType(ASTAssignmentExpression.class);
				if(assignmentExpression.jjtGetNumChildren() == 1) {
					ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression) assignmentExpression.getFirstChildOfType(ASTPrimaryExpression.class);
					if(astPrimaryExpression.isMethod()) {
						if(list_outsource.contains(astPrimaryExpression.getImage())) {
							type = VexNodeType.TYPE_6.name();
						}
						else {
							type = VexNodeType.TYPE_1.name();
						}
					}
					else {
						type = VexNodeType.TYPE_7.name();
					}
				}
				else if(assignmentExpression.jjtGetNumChildren() == 3) {
					type = VexNodeType.TYPE_4.name();
				}
			}
		}
		return type;
	}
}
