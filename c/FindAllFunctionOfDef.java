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

//��������ⲿ����Դ�������Ϣ
public class FindAllFunctionOfDef {
	
	private List<String> list = new ArrayList<String>();
	
	public static void main(String[] args) throws Exception{
		Graph_Info h = new Graph_Info();
//		StatementFeature sf = new StatementFeature();
		//��������ļ�·��
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
				//���FunctionDefinitation
				ASTFunctionDefinition function = (ASTFunctionDefinition)node;
				
				//��дast��Xpath
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
						System.out.println("�ļ�·��: "+args[1]);
						System.out.println("��������"+function.getImage());
						System.out.println("�кţ�"+s.getBeginLine());
				
						
						list_funcOfDef.add(list);
					}
				
				}
			}
		}
		
	
	}
	
	public List<List<String>> getList() {
		return list_funcOfDef;
	}
	
	//�ҵ������Զ��巽��
	private static List<List<String>> list_funcOfDef = new ArrayList<>();
	private List<String> list_outsource = new ArrayList<String>();
	/**���C�����г��õ��ⲿ���뺯��*/
	public void getReservedWords(){
		File file = new File("./outputlib.txt");
        BufferedReader reader = null;
        String str = "";  
        try{
            reader = new BufferedReader(new FileReader(file));
            String tempString = null;
            // һ�ζ���һ�У�ֱ������nullΪ�ļ�����
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
