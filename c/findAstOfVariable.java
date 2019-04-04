package softtest.depchain.c;


import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import softtest.CharacteristicExtract.c.Graph_Info;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.cfg.c.VexNode;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.NameOccurrence;
import sun.java2d.pipe.SpanShapeRenderer.Simple;

//寻找使用点和定义点，并将符号获取
public class findAstOfVariable {
	
	private List<String> list_def = new ArrayList<String>();
	private static List<String> list_use = new ArrayList<String>();
	private static List<String> list_operator = new ArrayList<String>();
	
	public static void main(String[] args) throws Exception{
		Graph_Info h = new Graph_Info();

		String filePath = args[1];
		List<CVexNode> list_cvex = new ArrayList<CVexNode>();
		list_cvex = h.getCVexNode(filePath);
		
		findAstOfVariable tg = new findAstOfVariable();
		//System.out.println(sf.getSelfStatementsFeature(filePath, "switchtest", 48, 57));
		ControlFlowVisitor cfv = new ControlFlowVisitor(filePath);
		ControlFlowData flow = new ControlFlowData();
		//System.out.println(list_cvex.size());
		//ASTTranslationUnit aa = new ASTTranslationUnit();
	
		
		for(CVexNode c : list_cvex){
			SimpleNode node = c.getMethodNameDeclaration().getNode();
			List<String> a = new ArrayList<String>();
			if (node instanceof ASTFunctionDefinition){
				ASTFunctionDefinition function = (ASTFunctionDefinition)node;
				String Xpath = ".//DirectDeclarator[@FunctionName='false']";
				List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
				evaluationResults = StateMachineUtils.getEvaluationResults(node, Xpath);
				for(SimpleNode s : evaluationResults){
					String string = s.getImage() + ":" + s.getBeginLine();
					tg.list_def.add(string);
				}
			   Xpath = ".//Expression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='false']";
			   evaluationResults.clear();
			   evaluationResults = StateMachineUtils.getEvaluationResults(node, Xpath);
				for(SimpleNode s : evaluationResults){
					String string = s.getImage() + ":" + s.getBeginLine();
					tg.list_def.add(string);
				}
			}
			
		}
		
		for(CVexNode c : list_cvex){
			SimpleNode node = c.getMethodNameDeclaration().getNode();
			List<String> a = new ArrayList<String>();
			if (node instanceof ASTFunctionDefinition){
				ASTFunctionDefinition function = (ASTFunctionDefinition)node;
				String Xpath = ".//Expression/AssignmentExpression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='false'][@Leaf='true']";
				List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
				evaluationResults = StateMachineUtils.getEvaluationResults(node, Xpath);
				for(SimpleNode s : evaluationResults){
					String string = s.getImage() + ":" + s.getBeginLine();
					tg.list_use.add(string);
				}
				Xpath = ".//AssignmentExpression/AdditiveExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='false'][@Leaf='true']";
				evaluationResults.clear();
				evaluationResults = StateMachineUtils.getEvaluationResults(node, Xpath);
				for(SimpleNode s : evaluationResults){
					String string = s.getImage() + ":" + s.getBeginLine();
					tg.list_use.add(string);
				}
			}
			
		}
		
		for(CVexNode c : list_cvex){
			SimpleNode node = c.getMethodNameDeclaration().getNode();
//			List<String> a = new ArrayList<String>();
			if (node instanceof ASTFunctionDefinition){
//				ASTFunctionDefinition function = (ASTFunctionDefinition)node;
				String Xpath = ".//AssignmentOperator";
				List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
				evaluationResults = StateMachineUtils.getEvaluationResults(node, Xpath);
				for(SimpleNode s : evaluationResults){
					String string = s.getOperators()+ ":" + s.getBeginLine();
					tg.list_operator.add(string);
				}
			}
			
		}
		
		
		//对定义点排序，以行号由小到大的规则排序
		Collections.sort(tg.list_def, new Comparator<String>() {  
		    @Override  
		    public int compare(String o1, String o2) {  
		    	o1 = o1.split(":")[1];
		    	o2 = o2.split(":")[1];
		        int x1 = Integer.parseInt(o1);  
		        int x2 = Integer.parseInt(o2);  
		        return x1>x2?1:(x1==x2?0:-1);  
		    }  
		});  
		
		//对使用点排序，以行号由小到大的规则排序
		Collections.sort(tg.list_use, new Comparator<String>() {  
		    @Override  
		    public int compare(String o1, String o2) { 
		    	o1 = o1.split(":")[1];
		    	o2 = o2.split(":")[1];
		        int x1 = Integer.parseInt(o1);  
		        int x2 = Integer.parseInt(o2);  
		        return x1>x2?1:(x1==x2?0:-1);  
		    }  
		});  
		

//		for(String str : tg.list_def){
//			System.out.println("定义点："+str);	
//		}
//		
//		for(String str : tg.list_use){
//			System.out.println("使用点："+str);	
//		}
//		
//		for(String str : tg.list_operator){
//			System.out.println("符号："+str);	
//		}
	}
	
	/*判断定义点是否为常量定义*/
	public boolean isDefOfConstant(NameOccurrence occ) {
		SimpleNode node = occ.getLocation();
		if (node instanceof ASTFunctionDefinition){
			ASTFunctionDefinition function = (ASTFunctionDefinition)node;
			String Xpath = ".//PrimaryExpression[@Leaf='true']";
			List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
			evaluationResults = StateMachineUtils.getEvaluationResults(node, Xpath);
			if(evaluationResults.size() == 0) {
				return true;
			}
		}
		return false;
	}
	
	public List<String> getList_Operator() {
		return list_operator;
	}
	
}
