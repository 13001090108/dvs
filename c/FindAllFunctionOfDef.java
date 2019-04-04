package softtest.depchain.c;


import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import softtest.CharacteristicExtract.c.Graph_Info;
import softtest.CharacteristicExtract.c.StatementFeature;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.cfg.c.VexNode;
import softtest.rules.c.StateMachineUtils;

//输出所有外部输入源的相关信息
public class FindAllFunctionOfDef {
	
	private List<String> list = new ArrayList<String>();
	
	public static void main(String[] args) throws Exception{
		Graph_Info h = new Graph_Info();
//		StatementFeature sf = new StatementFeature();
		//输入测试文件路径
		String filePath = args[1];
		List<CVexNode> list_cvex = new ArrayList<CVexNode>();
		list_cvex = h.getCVexNode(filePath);
		
		FindAllFunctionOfDef tg = new FindAllFunctionOfDef();
		tg.getReservedWords();
		
		//System.out.println(sf.getSelfStatementsFeature(filePath, "switchtest", 48, 57));
		ControlFlowVisitor cfv = new ControlFlowVisitor(filePath);
		ControlFlowData flow = new ControlFlowData();
		//System.out.println(list_cvex.size());
		//ASTTranslationUnit aa = new ASTTranslationUnit();
		
	
		
		for(CVexNode c : list_cvex){
			SimpleNode node = c.getMethodNameDeclaration().getNode();
			
			
			List<String> a = new ArrayList<String>();
			if (node instanceof ASTFunctionDefinition){
				//获得FunctionDefinitation
				ASTFunctionDefinition function = (ASTFunctionDefinition)node;
				
				//书写ast的Xpath
				String Xpath = ".//PrimaryExpression[@Method='true']";
				
//				String Xpath = ".//DirectDeclarator";
				List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
				evaluationResults = StateMachineUtils.getEvaluationResults(node, Xpath);
			
				
				for(SimpleNode s : evaluationResults){
					VexNode vexNode = s.getCurrentVexNode();
//					System.out.println(vexNode);
//					System.out.println(s+" "+s.getBeginLine());
					String string = s.getImage();
					if(!tg.list_outsource.contains(string)) {
						List<String> list = new ArrayList<>();
						list.add(args[1]);
						list.add(function.getImage());
						list.add(""+s.getBeginLine());
//						list.add(string);
						System.out.println("文件路径: "+args[1]);
						System.out.println("方法名："+function.getImage());
						System.out.println("行号："+s.getBeginLine());
				
						
						list_funcOfDef.add(list);
					}
				
				}
			}
		}
		
	
	}
	
	public List<List<String>> getList() {
		return list_funcOfDef;
	}
	
	//找到所有自定义方法
	private static List<List<String>> list_funcOfDef = new ArrayList<>();
	private List<String> list_outsource = new ArrayList<String>();
	/**获得C语言中常用的外部输入函数*/
	public void getReservedWords(){
		File file = new File("./outputlib.txt");
        BufferedReader reader = null;
        String str = "";  
        try{
            reader = new BufferedReader(new FileReader(file));
            String tempString = null;
            // 一次读入一行，直到读入null为文件结束
            while ((tempString = reader.readLine()) != null) {        
            	str += tempString;           
            }
            reader.close();
            String[] str_reserved = str.split(" ");
            for(int i = 1; i < str_reserved.length; i++){
            	list_outsource.add(str_reserved[i]);
            }        
        }catch(IOException e){
            e.printStackTrace();
        }
	}
}
