package softtest.depchain.c;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
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
import softtest.interpro.c.InterContext;
import softtest.rules.c.StateMachineUtils;

//输出所有外部输入源的相关信息
public class test_outputlib {
	
	private List<String> list = new ArrayList<String>();
	private List<String> files = new ArrayList<String>(); // 用于存储收集到的所有.c文件
	private HashMap<String, Graph> cfgmap = new HashMap<String, Graph>();
	
	public static void main(String[] args) throws Exception{
		Graph_Info h = new Graph_Info();

		Init init = new Init(args);	
		init.main(args);
		
//		StatementFeature sf = new StatementFeature();
		//输入测试路径
//		args[0] = "E:\\TESTCASE\\单元内\\test\\2.c";
		String filePath = args[0];

		
		test_outputlib tg = new test_outputlib();
		
		tg.cfgmap = init.getCfgmap();
		tg.getReservedWords();
		
		tg.collect(new File(filePath));
		
		for(String path : tg.files) {
		
		List<CVexNode> list_cvex = new ArrayList<CVexNode>();
		list_cvex = h.getCVexNode(path);

	
		
		//System.out.println(sf.getSelfStatementsFeature(filePath, "switchtest", 48, 57));
		ControlFlowVisitor cfv = new ControlFlowVisitor(path);
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

//					VexNode vexNode = s.getCurrentVexNode();
//					System.out.println(vexNode);
//					System.out.println(s+" "+s.getBeginLine());
					String string = s.getImage();
					if(tg.list_outsource.contains(string)) {
						List<String> list = new ArrayList<>();
						list.add(path);
						list.add(function.getImage());
						list.add(""+s.getBeginLine());
//						list.add(function.getImage());
						System.out.println("文件路径: "+path);
						System.out.println("方法名："+function.getImage());
						System.out.println("行号："+s.getBeginLine());
						System.out.println("外部输入源:"+string);
						
					
						
						if(init.getCfgmap().containsKey(function.getImage())) {
							Graph graph = init.getCfgmap().get(function.getImage());
							for(VexNode vexNode : graph.getAllnodes()) {
								if(vexNode.getTreenode().getBeginLine() == s.getBeginLine()) {
									System.out.println("输入源对应的vexNode节点： " + vexNode);
									list.add(vexNode.toString());
									break;
								}
							}
//							System.err.println(graph);
						}
						
						list_out.add(list);
					}
				
				}
			}
		}
	  }
	}
	
	// 收集测试路径下的所有.C源文件
	private void collect(File srcFileDir) {
		if (srcFileDir.isFile() && srcFileDir.getName().matches(InterContext.SRCFILE_POSTFIX)) {
			files.add(srcFileDir.getPath());
		} else if (srcFileDir.isDirectory()) {
			File[] fs = srcFileDir.listFiles();
			for (int i = 0; i < fs.length; i++) {
				collect(fs[i]);
			}
		}
	}
	
	public List<List<String>> getList() {
		return list_out;
	}
	
	public List<String> getlist_outsource() {
		return list_outsource;
	}
	
	private static List<List<String>> list_out = new ArrayList<>();
	private static List<String> list_outsource = new ArrayList<String>();
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
