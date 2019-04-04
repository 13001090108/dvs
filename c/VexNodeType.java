package softtest.depchain.c;

import java.util.List;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;

/**
 *
 *对控制流节点类型进行判断
 *type == 0 控制流图入口节点
 *type == 1 只有函数 f()或者f(c)
 *type == 2 有定义声明 ： 例如 int c = m + f();
 *type == 3 有定义声明(仅仅声明，未赋值) , 例如int c;
 *type == 4 无定义声明 ： 例如 c = m + a;
 *type == 5 控制流图出口节点
 *type == 6 库函数
 *type == 7 其他情况 比如c ++
 *type == 8 无内容节点
 */
public  enum VexNodeType {
	/**
	 * 控制流图入口节点",0
	 */
	TYPE_0("控制流图入口节点",0),
	/**"只有函数 f()或者f(c)",1 */
	TYPE_1("只有函数 f()或者f(c)",1),
	/**"有定义声明 ", 2 */
	TYPE_2("有定义声明",2),
	/***    "有定义声明(仅仅声明，未赋值)",3   */
	TYPE_3("有定义声明(仅仅声明，未赋值)",3),
	/** "无定义声明",4 */
	TYPE_4("无定义声明",4),
	/**"控制流图出口节点",5*/
	TYPE_5("控制流图出口节点",5),
	/**"库函数",6**/
	TYPE_6("库函数",6),
	/***"其他情况，比如自增自减操作",7*/
	TYPE_7("其他情况,",7),
	/**"无内容节点",8**/
	TYPE_8("无内容节点",8)
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
	 * 判断传入控制流节点类型
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
