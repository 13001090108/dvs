package softtest.depchain.c;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.jaxen.JaxenException;

import softtest.CharacteristicExtract.c.Graph_Info;
import softtest.CharacteristicExtract.c.StatementFeature;
import softtest.CharacteristicExtract.c.test;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.cfg.c.VexNode;
import softtest.interpro.c.InterContext;
import softtest.rules.c.StateMachineUtils;

//找到所有函数的依赖
public class SearchFunction {

	private List<String> list = new ArrayList<String>();
	private List<String> files = new ArrayList<String>(); // 用于存储收集到的所有.c文件

	public static void main(String[] args) throws Exception {
		Graph_Info h = new Graph_Info();
		// StatementFeature sf = new StatementFeature();
		// 输入测试文件路径
		String Path = args[0];

		SearchFunction tg = new SearchFunction();
		tg.getReservedWords();
        
		tg.collect(new File(Path));

		// add by lsc 2019/1/1 用于记录函数的名称与其声明路径的映射
		for (String filePath : tg.files) {

			List<CVexNode> list_cvex = new ArrayList<CVexNode>();
			list_cvex = h.getCVexNode(filePath);

			// System.out.println(sf.getSelfStatementsFeature(filePath,
			// "switchtest", 48, 57));
			ControlFlowVisitor cfv = new ControlFlowVisitor(filePath);
			ControlFlowData flow = new ControlFlowData();
			// System.out.println(list_cvex.size());
			// ASTTranslationUnit aa = new ASTTranslationUnit();

			for (CVexNode c : list_cvex) {
				SimpleNode node = c.getMethodNameDeclaration().getNode();

				if (node instanceof ASTFunctionDefinition) {
					// 获得FunctionDefinitation
					ASTFunctionDefinition function = (ASTFunctionDefinition) node;

					ASTDirectDeclarator astDirectDeclarator = (ASTDirectDeclarator) function
							.getFirstChildOfType(ASTDirectDeclarator.class);

					String string = astDirectDeclarator.getImage();
					if (!tg.list_reserved.contains(string)) {

						// add by lsc 2019/1/1 用于记录函数的名称与其声明路径的映射
						if (!map_function_path.containsKey(function.getImage())) {
							map_function_path.put(function.getImage(), filePath);
						}
						
						// add by lsc 2019/1/1 用于记录函数的名称与对应抽象语法树节点
						if(!map_function_simpleNode.containsKey(function.getImage())) {
							map_function_simpleNode.put(function.getImage(), function);
						}
					}
				}
			}
		}
		
		
		for(Map.Entry<String, String> entry : map_function_path.entrySet()) {
			System.err.println(entry.getKey()+":"+entry.getValue()+ ":" +map_function_simpleNode.get(entry.getKey()).getBeginLine());
		}
		
		

		for (String filePath : tg.files) {

			List<CVexNode> list_cvex = new ArrayList<CVexNode>();
			list_cvex = h.getCVexNode(filePath);

			// System.out.println(sf.getSelfStatementsFeature(filePath,
			// "switchtest", 48, 57));
			ControlFlowVisitor cfv = new ControlFlowVisitor(filePath);
			ControlFlowData flow = new ControlFlowData();
			// System.out.println(list_cvex.size());
			// ASTTranslationUnit aa = new ASTTranslationUnit();

			for (CVexNode c : list_cvex) {
				SimpleNode node = c.getMethodNameDeclaration().getNode();

				if (node instanceof ASTFunctionDefinition) {
					// 获得FunctionDefinitation
					ASTFunctionDefinition function = (ASTFunctionDefinition) node;

					// 书写ast的Xpath
					String Xpath = ".//PrimaryExpression[@Method='true']";

					// String Xpath = ".//DirectDeclarator";
					List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
					evaluationResults = StateMachineUtils.getEvaluationResults(node, Xpath);

					List<String> list_strings = new ArrayList<>();
					for (SimpleNode s : evaluationResults) {
						VexNode vexNode = s.getCurrentVexNode();
						// System.out.println(vexNode);
						// System.out.println(s+" "+s.getBeginLine());
						String string = s.getImage();
						if (!tg.list_reserved.contains(string)) {
							List<String> list = new ArrayList<>();

							list.add(function.getImage());
							list.add("" + s.getBeginLine());
							list.add(string);
							System.out.println("文件路径: " + filePath);
							System.out.println("方法名：" + function.getImage());
							System.out.println("被调用方法在调用方法中的行号：" + s.getBeginLine());
							System.out.println("被调用方法:" + string);
							System.out.println("被调用方法所在路径: " + map_function_path.get(function.getImage()));

							if ((!(map_function_path.get(string) == null)) && (!map_function_path.get(string).equals(filePath))) {
								System.err.println("文件路径: " + filePath);
								System.err.println("方法名：" + function.getImage());
								System.err.println("被调用方法在调用方法中的行号：" + s.getBeginLine());
								System.err.println("被调用方法:" + string);
								System.err.println("被调用方法所在路径: " + map_function_path.get(string));

							}

							// 记录函数与其被调用函数集合的map
							if (!map_function.containsKey(string)) {
								List<String> list2 = new ArrayList<>();
								list2.add(function.getImage());
								map_function.put(string, list2);
							} else {
								System.out.println(map_function.get(string) + "  map_function:" + map_function + " "
										+ "string: " + string);
								System.out.println(function.getImage());
								if (!(map_function.get(string) == null ) && !map_function.get(string).contains(function.getImage())) {
									map_function.get(string).add(function.getImage());
								}
							   if(map_function.get(string) == null) {
									List<String> list2 = new ArrayList<>();
									list2.add(function.getImage());
									map_function.put(string, list2);
								}
							}

							// 记录函数与其调用的函数集合的map
							if (!map_function_contains.containsKey(function.getImage())) {
								List<String> list3 = new ArrayList<>();
								list3.add(string);
								map_function_contains.put(function.getImage(), list3);
							} else {
								if (!map_function_contains.get(function.getImage()).contains(string)) {
									map_function_contains.get(function.getImage()).add(string);
								}
							}

							if (!list_function.contains(string)) {
								list_function.add(string);
							}
							if (!list_function.contains(function.getImage())) {
								list_function.add(function.getImage());
							}
						}

					}
				}
			}

			System.out.println("输出list_function:");
			System.out.println(list_function);
			for (String string : list_function) {
				if (!map_function.containsKey(string)) {
					map_function.put(string, null);
				}
			}

			System.out.println("输出map_function:");
			for (Entry<String, List<String>> entry : map_function.entrySet()) {
				System.out.println(entry.getKey() + ":" + entry.getValue());
			}

			System.out.println("输出map_function_contains:");
			for (Entry<String, List<String>> entry : map_function_contains.entrySet()) {
				System.out.println(entry.getKey() + ":" + entry.getValue());
			}
		}

	}

	public List<String> getList() {
		return list_function;
	}

	public Map<String, List<String>> getMapOfFunction() {
		return map_function;
	}

	public Map<String, List<String>> getMapOfFunctionContains() {
		return map_function_contains;
	}

	// 所有的自定义函数集合
	private static List<String> list_function = new ArrayList<>();
	// 函数与其被调用函数集合的映射
	private static Map<String, List<String>> map_function = new HashMap<>();
	// 函数与其调用函数集合的映射
	private static Map<String, List<String>> map_function_contains = new HashMap<>();
	private List<String> list_reserved = new ArrayList<String>();

	// add by lsc 2019/1/1 用于记录函数的名称与其声明路径的映射
	private static Map<String, String> map_function_path = new HashMap<>();
	// add by lsc 2019/1/1 用于记录函数的名称与对应抽象语法树节点
	private static Map<String, SimpleNode> map_function_simpleNode = new HashMap<>();

	public Map<String, String> getMap_Function_Path() {
		return map_function_path;
	}
	public Map<String, SimpleNode> getMap_Function_SimpleNode() {
		return map_function_simpleNode;
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

	/** 获得C语言中的保留字 */
	public void getReservedWords() {
		File file = new File("./reserved.txt");
		BufferedReader reader = null;
		String str = "";
		try {
			reader = new BufferedReader(new FileReader(file));
			String tempString = null;
			// 一次读入一行，直到读入null为文件结束
			while ((tempString = reader.readLine()) != null) {
				str += tempString;
			}
			reader.close();
			String[] str_reserved = str.split(" ");
			for (int i = 1; i < str_reserved.length; i++) {
				list_reserved.add(str_reserved[i]);
			}
//			for (int i = 1; i < str_reserved.length; i++) {
//				System.out.println(str_reserved[i]);
//			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

}
