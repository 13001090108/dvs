package softtest.depchain.c;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;

import javax.print.attribute.SetOfIntegerSyntax;
import javax.sound.midi.SysexMessage;

import org.apache.tools.ant.filters.FixCrLfFilter.AddAsisRemove;
import org.apache.tools.ant.taskdefs.PathConvert.MapEntry;
import org.jaxen.JaxenException;

import org.omg.CORBA.PRIVATE_MEMBER;

import com.alibaba.fastjson.JSON;
import com.alibaba.fastjson.JSONArray;
import com.alibaba.fastjson.JSONObject;
import com.sun.org.apache.bcel.internal.generic.IFGE;
import com.sun.org.apache.bcel.internal.generic.RETURN;
import com.sun.org.apache.xml.internal.resolver.helpers.PublicId;
import com.sun.swing.internal.plaf.basic.resources.basic;
import com.sun.tracing.dtrace.ArgsAttributes;
import com.sun.xml.internal.bind.v2.runtime.Name;

import softtest.CharacteristicExtract.c.Graph_Info;
import softtest.CharacteristicExtract.c.StatementFeature;
import softtest.CharacteristicExtract.c.test;
import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTFunctionDeclaration;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTNestedFunctionDefinition;
import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.CParserVisitor;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CEdge;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;
import softtest.cfg.c.VexNode;

import softtest.depchain.c.DepChainUtil.listSCVPVisitor;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.analysis.ValueSet;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.interpro.c.Method;
import softtest.interpro.c.MethodNode;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.rules.c.StateMachineUtils;
import softtest.rules.gcc.fault.OOB_CheckStateMachine;
import softtest.scvp.c.Position;
import softtest.scvp.c.SCVP;
import softtest.scvp.c.SCVPString;
import softtest.scvp.c.SCVPVisitor;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;
import sun.net.www.content.text.plain;

public class DepChainSimple implements Serializable {
	/**
	 * 序列化ID
	 */
	private static final long serialVersionUID = 5802149016969017989L;
	private List<AnalysisElement> elements = new ArrayList<AnalysisElement>();;
	private String analysisDir = "";
	private List<String> files = new ArrayList<String>(); // 用于存储收集到的所有.c文件
	private InterCallGraph interCGraph = InterCallGraph.getInstance(); // 得到包含这些函数的文件的依赖关系
	private String[] args;
	private Pretreatment pre = new Pretreatment();

	public DepChainSimple(String[] args) {

		// add by lsc 2018/9/20
		// 此处为分析路径下的文件，args[0]表示分析路径下的所有.c文件，args[1]表示分析指定的.c文件
		this.analysisDir = args[1];
		this.setArgs(args);
		init();
	}

	private HashMap<String, ASTTranslationUnit> astmap = new HashMap<String, ASTTranslationUnit>();
	private HashMap<String, Graph> cfgmap = new HashMap<String, Graph>();
	private HashMap<Graph, String> cfgmap2 = new HashMap<Graph, String>();
	private HashMap<String, CGraph> cgMap = new HashMap<String, CGraph>();

	// add by lsc 2018/10/26 用于得到溯源过程中所有相关函数包含的全部的变量的NameOccurence
	private static Set<NameOccurrence> set2 = new HashSet<>();

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

	// 进行预编译的初始化
	private void init() {
		pre.setPlatform(PlatformType.GCC);

		File srcFileDir = new File(analysisDir);
		collect(srcFileDir);
	}

	
	public List<List<String>> list_out = new ArrayList<>();
	public List<List<String>> list_out_thisfile = new ArrayList<>();
	public List<String> list_function = new ArrayList<>();
	public List<String> list_operator = new ArrayList<>();
	// add by lsc 用于记录所有函数与其被调用函数集合的映射
	public Map<String, List<String>> map_function = new HashMap<>();
	// add by lsc 2018/11/27晚 用于记录所有函数与其调用函数集合的映射
	public Map<String, List<String>> map_function_contains = new HashMap<>();
	// add by lsc 2018/11/27 用于记录溯源变量过程中函数与其被调用函数集合的映射
	public Map<String, List<String>> map_function_internal = new HashMap<>();

	// add by lsc 2018/11/27晚，用于记录溯源变量过程中路径与对应需要高亮的函数集合的映射
	public Map<List<String>, List<List<String>>> Map_path_HighlightFunction = new HashMap<>();

	// add by lsc 2018/11/28,用于记录对应每路径需要高亮的函数集合
	public List<Set<String>> HighlightFunction = new ArrayList<>();

	// add by lsc 2018/11/29，用于记录与变量相关的外部输入源
	public List<List<String>> list_out_variable = new ArrayList<>();

	// add by lsc 2018/11/29 , 用于记录相应行号与此行的外部输入源的映射
	public Map<VexNode, List<String>> map_line_list_out_variable = new HashMap<>();
	
	// add by lsc 2019/1/2 用于记录函数的名称与其声明路径的映射
	public Map<String, String> map_function_path = new HashMap<>();
	// add by lsc 2019/1/2 用于记录函数的名称与对应抽象语法树节点的映射
	public Map<String, SimpleNode> map_function_simpleNode = new HashMap<>();

	public static void main(String[] args) throws Exception {
		DepChainSimple test = new DepChainSimple(args);
		// int type = Integer.valueOf(args[5]);
		// if (type == 1) {
		// // add by lsc 2018/11/12记录外部输入源
		// System.out.println(test.analyse1());
		// }

		// motified by lsc 2018/11/29，无论参数如何，先将外部输入源获取
		// add by lsc 2018/11/12记录外部输入源
		System.out.println(test.analyse1());
		
		

		if (args.length == 5) {
			
//			test.prepare();
			
			System.out.println(test.analyse2());// 输入域分析

			// 与变量相关的外部输入源获取
			test.list_out_variable = test.getList_Out_Valiable(test.getmap_line_list_out_variable());

			test.analyse3();
			System.out.println("pathSet3: " + test.pathSet3);
			
			//add by lsc 2019/1/2 用于获取函数的名称与对应抽象语法树节点的映射，以及函数名称与对应文件的映射
//			for(Map.Entry<String, String> entry : test.map_function_path.entrySet()) {
//				System.err.println("mmmm"+entry.getKey()+":"+entry.getValue()+ ":" +test.map_function_simpleNode.get(entry.getKey()).getBeginLine());
//			}
			
		

			System.out.println("溯源路径函数的相关内嵌函数映射:");
			Set<String> set = null;

			for (String string : test.pathSet3) {
				set = new HashSet<>();
				String[] strings = string.split("<-");

				for (String string2 : strings) {
					set.add(string2);
				}
			}

		
			for (String string : set) {
				if (test.map_function_contains.containsKey(string)) {
					test.map_function_internal.put(string, test.map_function_contains.get(string));
				}
			}
			
			
			System.out.println("输出map_function_internal: ");
			for(Map.Entry<String, List<String>>entry : test.map_function_internal.entrySet()) {
				System.out.println(entry.getKey()+":"+entry.getValue());
			}
			
			

			// 操作HightlightFunction
			for (String string : test.pathSet3) {
				Set<String> set2 = new HashSet<>();
				String[] strings = string.split("<-");
				for (String string2 : strings) {
					// add by lsc 2018/11/28
					// 用于解决路径中可能包含map2中不存在的函数的情况(因为路径调用计算，而map2需变量参与，故
					// 若是返回值函数f()只被调用而不被赋值，则此情况会发生)
					if (test.map2.containsKey(string2)) {
						set2.add(string2);
						if (test.map_function_contains.containsKey(string2)) {
							for (String string3 : test.map_function_contains.get(string2)) {
								if (test.map2.containsKey(string3)) {
									set2.add(string3);
								}
							}
						}
					}

				}

				test.HighlightFunction.add(set2);
			}

			// for(Entry<String, List<String>> entry :
			// map_function_internal.entrySet()) {
			// System.out.println(entry.getKey()+":" + entry.getValue());
			// }

			System.out.println("输出HighlightFunction:");
			for (Set<String> set2 : test.HighlightFunction) {
				for (String string : set2) {
					System.out.print(string + " ");
				}
				System.out.println();
			}

			System.out.println("输出高亮函数：");
			for (Set<String> set1 : test.HighlightFunction) {

				System.out.println(set1);
			}
		}
		if (args.length == 4) {
			System.out.println(test.analyse3());
		} else {
			if (args.length <= 2) {

			}
		}
		// if(args.length == 5) {
		// test.map2 = test.analyse2();
		// System.out.println(test.map2.size());
		//
		// for(Entry<String, Set<Integer>> entry : test.map2.entrySet()) {
		// String string = entry.getKey();
		// Set<Integer>set = entry.getValue();
		// System.out.println("函数："+string +" "+"高亮行号："+set);
		// }
		//
		// test.analyse3();
		// for(Set<String>set :test.HighlightFunction) {
		// for(String string : set) {
		// System.out.print(string+" ");
		// }
		// System.out.println();
		// }
		// }
		// if(args.length == 4) {
		// System.out.println(test.analyse3());
		// }

	}
	

	

	public HashSet<String> pathSet3 = new HashSet<String>();

	public void getpathSet3(String function, String path) {
		if (map_function.get(function) == null) {
			pathSet3.add(path);
		} else {
			for (String string : map_function.get(function)) {

				getpathSet3(string, path + "<-" + string);
			}
		}

	}

	/**
	 * 对所有.C源文件依次进行处理：预编译、分析、生成全局函数调用关系图
	 * 
	 * @throws IOException
	 */
	private void process() throws IOException {
		// 第一步：对所有.C源文件进行预编译
		PreAnalysis();

		// 第二步：生成全局函数调用关系图
		List<AnalysisElement> orders = interCGraph.getAnalysisTopoOrder();
		if (orders.size() != elements.size()) {
			for (AnalysisElement element : elements) {
				boolean exist = false;
				for (AnalysisElement order : orders) {
					if (order == element) {
						exist = true;
					}
				}
				if (!exist) {
					orders.add(element);
				}
			}
		}
	}

	private void PreAnalysis() {
		for (String srcFile : files) {
			AnalysisElement element = new AnalysisElement(srcFile);
			elements.add(element);
			// 预编译之后的.I源文件
			String afterPreprocessFile = null;
			List<String> include = new ArrayList<String>();
			include.add("C:/Program Files (x86)/DTS/DTS/DTSGCC/include");
			List<String> macro = new ArrayList<String>();
			afterPreprocessFile = pre.pretreat(srcFile, include, macro);// 调用各编译器的预处理指令生成中间文件

			try {
				String temp = element.getFileName();
				// 产生抽象语法树
				System.out.println("生成抽象语法树...");
				System.out.println(afterPreprocessFile);
				CParser parser = CParser.getParser(new CCharStream(new FileInputStream(afterPreprocessFile)));
				ASTTranslationUnit root = parser.TranslationUnit();
				astmap.put(srcFile, root);// 把语法树扔内存里，通过文件名检索

				// 产生符号表
				System.out.println("生成符号表...");
				ScopeAndDeclarationFinder sc = new ScopeAndDeclarationFinder();
				root.jjtAccept(sc, null);
				OccurrenceAndExpressionTypeFinder o = new OccurrenceAndExpressionTypeFinder();
				root.jjtAccept(o, null);

				// 生成全局函数调用关系
				System.out.println("生成全局函数调用关系...");
				root.jjtAccept(new InterMethodVisitor(), element);

				// 文件内函数调用关系图
				System.out.println("生成文件内函数调用关系...");
				CGraph g = new CGraph();
				((AbstractScope) (root.getScope())).resolveCallRelation(g);
				List<CVexNode> list = g.getTopologicalOrderList(element);
				Collections.reverse(list);
				cgMap.put(srcFile, g);

				// 生成控制流图
				System.out.println("生成控制流图...");
				ControlFlowVisitor cfv = new ControlFlowVisitor(element.getFileName());
				ControlFlowData flow = new ControlFlowData();
				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
						cfv.visit((ASTFunctionDefinition) node, flow);
						cfgmap.put(node.getImage(), ((ASTFunctionDefinition) node).getGraph());
						cfgmap2.put(((ASTFunctionDefinition) node).getGraph(), node.getImage());

						// add test by lsc 2018/11/22
						// System.out.println("============"+node.getImage()+":"+node.getBeginLine());
						// Graph graph = ((ASTFunctionDefinition)
						// node).getGraph();
						// List<VexNode> list2 = graph.getAllnodes();
						// System.out.println(list2.size()+"个节点");
					}
				}

				// 生成定义使用链
				System.out.println("生成定义使用链...");

				/**
				 * add by lsc 2018/9/14此处比较关键的调用了ASTTranslationUnit.java中的
				 * public Object jjtAccept(CParserVisitor visitor, Object data)
				 * 方法 DUAnalysisVisitor.java中的visit方法，
				 * 之后initDefUse(),再之后AbstractScope.java中的
				 * checkOccurrenceType()其中"进行修正"出现在NameOccurrence中
				 */
				root.jjtAccept(new DUAnalysisVisitor(), null);

				// 计算SCVP
				System.out.println("计算scvp...");

				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
						// System.out.println(cvnode.toString());

						node.jjtAccept(new SCVPVisitor(), null);

					}
				}
				System.out.println("OK.");

			} catch (Exception e) {
				e.printStackTrace();
			}

		}
	}

	public List<List<String>> analyse1() throws Exception {
		
		
		
		
		test_outputlib tg = new test_outputlib();
		String[] args1 = new String[1];
		// 此处可以传入璐璐鼠标点击获取的路径信息,2018/11/30 add by lsc
		args1[0] = args[1];
		tg.main(args1);
		list_out = tg.getList();
		return list_out;
	}

	// 全局变量map2中存储有每个函数中相关溯源点的行号
	private Map<String, Set<Integer>> map2 = new HashMap<>();

	public Map<String, Set<Integer>> analyse2() throws Exception {
//		findAstOfVariable findAstOfVariable = new findAstOfVariable();
//		findAstOfVariable.main(args);
//		list_operator = findAstOfVariable.getList_Operator();
//
//		System.out.println(list_operator.toString());

		process();
		getMap_function(cgMap);
		getList_function(cgMap);
		getMap_function_path(cgMap);
		getMap_function_simpleNode(cgMap);
		// 获取要求变量的NameOccurrence
		NameOccurrence occ = locate(args[1], args[2], args[3], Integer.valueOf(args[4]));
//        System.out.println("目标点："+occ.getOccurrenceType()+occ.toString());
//       
	
		// VexNode vexNode = occ.getLocation().getCurrentVexNode();
 
		generate2(occ);

		System.out.println(vis.toString());
		System.out.println("信号量追踪情况：" + VariableOfSort.toString());

		System.out.println("map2:");
		return map2;
	}
	
	
	/**
	 * add by lsc 2019/3/12
	 * 获取函数名称与其对应的抽象语法树节点的映射
	 */
	public void getMap_function_simpleNode(HashMap<String, CGraph> cgMap) {
		for(String fString : files) {
			CGraph g = cgMap.get(fString);
			Hashtable<String, CVexNode> hashtable = g.nodes;
			Set<String> set = hashtable.keySet();
			for(String string : set) {
				CVexNode cVexNode = hashtable.get(string);
				String str = cVexNode.getMethodDeclaration().getImage();
				if(!map_function_simpleNode.containsKey(str)) {
					map_function_simpleNode.put(str, cVexNode.getMethodDeclaration());
					System.out.println(str+" : "+ cVexNode.getMethodDeclaration().getBeginLine());
				}
			}
		}
		System.out.println("map_function_simpleNode : "+ map_function_simpleNode);
	}
	
	/**
	 * add by lsc 2019/3/12
	 * 获取函数与其声明位置的映射
	 */
	public void getMap_function_path(HashMap<String, CGraph> cgMap) {
		for(String fString : files) {
			CGraph g = cgMap.get(fString);
			Hashtable<String, CVexNode> hashtable = g.nodes;
			Set<String> set = hashtable.keySet();
			for(String string : set) {
				CVexNode cVexNode = hashtable.get(string);
				String str = cVexNode.getMethodDeclaration().getImage();
				if(!map_function_path.containsKey(str)) {
					map_function_path.put(str, fString);
				}
			}
		}
		System.out.println("map_function_path : "+ map_function_path);
	}
	
	/**
	 * add by lsc 2019/3/12
	 * 获取所有自定义的方法的列表
	 */
	public void getList_function(HashMap<String, CGraph> cgMap) {
		for(String fString : files) {
			CGraph g = cgMap.get(fString);
			Hashtable<String, CVexNode> hashtable = g.nodes;
			Set<String> set = hashtable.keySet();
			for(String string : set) {
				CVexNode cVexNode = hashtable.get(string);
				String str = cVexNode.getMethodDeclaration().getImage();
				if(!list_function.contains(str)) {
					list_function.add(str);
				}
			}
		}
		System.out.println("list_function: " + list_function);
	}
	
	
	/**
	 * add by lsc 2019/3/12
	 * 获取函数与其被调用函数的映射
	 */
	public void getMap_function(HashMap<String, CGraph> cgMap) {
		//add test by lsc 2019/3/12
		for(String fString : files) {
			CGraph g = cgMap.get(fString);
			Hashtable<String, CEdge>hashtable = g.edges;
			Set<String> set = hashtable.keySet();
			for(String string : set ) {
				CEdge edge = hashtable.get(string);
				String end = edge.getTailNode().getMethodDeclaration().getImage();
				String start = edge.getHeadNode().getMethodDeclaration().getImage();
			
				if(!map_function.containsKey(start)) {
					List<String> list = new ArrayList<>();
					list.add(end);
					map_function.put(start, list);
				}
				else {
					List<String> list = map_function.get(start);
					list.add(end);
					map_function.put(start, list);
				}
				
				
			}
		
			
		}
		System.out.println("map_function : "+ map_function);
	}
	
	
	
	

	// public HashSet<String> pathSet = new HashSet<String>();
	// 应费克雄要求，将调用路径关系不以String类型存储以LinkedList方式存储
	public HashSet<String> pathSet = new HashSet<>();
	public LinkedList<String> linkedList = new LinkedList<>();

	/**
	 * 
	 * @param occ
	 */
	private void generate2(NameOccurrence occ) {
		DepGraphNode g = new DepGraphNode(occ);

		// 清空路径容器
		pathSet.clear();

		// 清空Set容器，用来准备存储变量信息(NameOccurrence),此set容器是用来遍历用
		vis.clear();
		VariableOfSort.clear();

		// 此dfs仅仅是模拟递归，无输出值，作用是为下面提供g,即全局变量，进而输出函数间的调用关系，和完成map2记录
		dfs(occ, g, 0, 1);

	}

	/**
	 * add by lsc 2018/12/1
	 * 
	 * @param occ
	 * @return
	 * @throws IOException
	 */
	public Map<VexNode, List<String>> getmap_line_list_out_variable() throws IOException {
		map_line_list_out_variable.clear();
		process();
		// 获取要求变量的NameOccurrence
		NameOccurrence occ = locate(args[1], args[2], args[3], Integer.valueOf(args[4]));

		DepGraphNode g = new DepGraphNode(occ);

		// 清空Set容器，用来准备存储变量信息(NameOccurrence),此set容器是用来遍历用
		vis.clear();

		// 此dfs仅仅是模拟递归，无输出值，作用是为下面提供g,即全局变量，进而输出函数间的调用关系，和完成map2记录
		dfs(occ, g, 0, 1);

		return map_line_list_out_variable;
	}

	/**
	 * 打印出函数内各个节点的scvp的信息
	 * 
	 * @param funcName
	 *            为了可序列化该方法能被调用，将其private修饰去除 2018/10/17 add by lsc
	 */
	void listSCVP(String funcName) {
		Graph cfg = cfgmap.get(funcName);
		JSONObject jsonObject = new JSONObject(true);

		GraphVisitor visitor = new DepChainUtil.listSCVPVisitor();
		cfg.numberOrderVisit(visitor, jsonObject);

		// modify by lsc 2018/9/18这句话要好好分析
		System.out.println(JSON.toJSONString(jsonObject, true));
	}

	private Map<String, Set<String>> vexMap = new HashMap<>();
	private Map<String, Boolean> condMap = new HashMap<>();
	private Map<String, Boolean> condLineMap = new HashMap<>();

	/*
	 * 获取函数间的调用路径关系信息 noted by lsc 2018/10/26
	 */
	private void dfsGetAllPath(DepGraphNode root, String path) {
		if (root.child == null || root.child.size() == 0) {
			pathSet.add(path);
		}
		String curFuncName = cfgmap2.get(root.occ.getLocation().getCurrentVexNode().getGraph());
		for (DepGraphNode child : root.child) {
			String childFuncname = cfgmap2.get(child.occ.getLocation().getCurrentVexNode().getGraph());

			if (!curFuncName.equals(childFuncname))

				dfsGetAllPath(child, path + "<-" + childFuncname);
			else
				dfsGetAllPath(child, path);
		}
	}

	private HashSet<NameOccurrence> vis = new HashSet<>();

	// add by lsc 2018/11/28晚，为了追踪信号量的分析情况
	private List<NameOccurrence> VariableOfSort = new ArrayList<>();

	/**
	 * 
	 * @param NameOccurrence
	 *            occ
	 * @param DepGraphNode
	 *            g
	 * @param int
	 *            cond
	 * @param int
	 *            depth
	 */

	private void dfs(NameOccurrence occ, DepGraphNode g, int cond, int depth) {
		if (vis.contains(occ)) {
			return;
		}
		vis.add(occ);
		VariableOfSort.add(occ);
		// count++;
		if (g == null)
			return;
		// if (depth > 5) return;

		try {

			// add by lsc 2018/10/24 获取函数名 (以下两种方式均可获取函数名)
			String func = ((ASTFunctionDefinition) occ.getLocation().getFirstParentOfType(ASTFunctionDefinition.class))
					.getImage();
			int line = Integer.valueOf(occ.toString().split(":")[1]);

			if (!map2.containsKey(func)) {
				map2.put(func, new HashSet<Integer>());
			}
			map2.get(func).add(line);

			// add by lsc 2018/11/29为了添加变量的外部输入源节点信息
			VexNode vexNode = occ.getLocation().getCurrentVexNode();
			// System.out.println("vexNode: lsc " + vexNode);

			List<NameOccurrence> list1 = vexNode.getOccurrences();

			for (List<String> list : list_out) {
				if (list.contains(args[1])) {
					list_out_thisfile.add(list);
				}
			}

			for (List<String> list : list_out_thisfile) {
				if (list.get(2) != null && list.get(2).equals(String.valueOf(line))) {
					if (!map_line_list_out_variable.containsKey(vexNode)) {

						map_line_list_out_variable.put(vexNode, list);
					}
				}
			}

			// add by lsc 2018/9/16
			if (cond == 1) {

				condLineMap.put(func + "_" + occ.toString().split(":")[1], true);
				// System.out.println(func +"_"+
				// occ.toString().split(":")[1]+"lsc");
				// g.setCond(true);
			} else {

			}
			if (occ == null)
				return;

			if (occ.getOccurrenceType() == OccurrenceType.USE) {

				// add by lsc 2018/12/4 增加了对数组的处理

				if (occ.getLocation().getOperators().equals("[")) {
					Graph graph = occ.getLocation().getCurrentVexNode().getGraph();
					System.err.println(graph);
					System.out.println(occ);

					// add by lsc 2018/12/7晚 ，若数组[]中不是变量而是常量。例如num[1]
					if (occ.toString().contains("[")) {
						VexNode cVexNode = null; // 用于记录occ前面变量中与occ距离最近的相同变量所在节点
						for (VexNode vexNode2 : graph.getAllnodes()) {
							for (NameOccurrence cNameOccurrence : vexNode2.getOccurrences()) {
								if (cNameOccurrence.toString().split(":")[0].equals(occ.toString().split(":")[0])
										&& vexNode2.getSnumber() < occ.getLocation().getCurrentVexNode().getSnumber()
										&& isOnLeftHandSideForArray(cNameOccurrence)) {
									cVexNode = vexNode2;
								}
							}
						}

						// 即前面有诸如num[1]赋值的定义变量
						if (cVexNode != null) {
							for (NameOccurrence cNameOccurrence : cVexNode.getOccurrences()) {

								DepGraphNode g2 = g.addChild(cNameOccurrence);
								dfs(cNameOccurrence, g2, cond, depth + 1);

							}
						}
						// 若前面没有num[1]赋值的定义变量，那就找num数组的定义点
						else {
							NameOccurrence nameOccurrence = occ;
							boolean flag = false;
							for (VexNode vexNode2 : graph.getAllnodes()) {
								for (NameOccurrence nameOccurrence1 : vexNode2.getOccurrences()) {
									if (nameOccurrence1.getLocation().getOperators().equals("[")) {
										nameOccurrence = nameOccurrence1;
										System.out.println(nameOccurrence + "lsc" + vexNode2);
										flag = true;
										break;
									}
								}
								if (flag) {
									break;
								}
							}
						}
					} else {
						NameOccurrence nameOccurrence = occ;
						boolean flag = false;
						for (VexNode vexNode2 : graph.getAllnodes()) {
							for (NameOccurrence nameOccurrence1 : vexNode2.getOccurrences()) {
								if (nameOccurrence1.getLocation().getOperators().equals("[")) {
									nameOccurrence = nameOccurrence1;
									System.out.println(nameOccurrence + "lsc" + vexNode2);
									flag = true;
									break;
								}
							}
							if (flag) {
								break;
							}
						}
						DepGraphNode g2 = g.addChild(nameOccurrence);
						dfs(nameOccurrence, g2, cond, depth + 1);
					}
				}

				// add by lsc 2018/12/6增加了对switch的间接控制处理

				// add by lsc 2018/12/7若不加这个则丢失了switch条件约束变量的继续追溯
				if (occ.getLocation().getCurrentVexNode().toString().contains("switch")) {
					List<NameOccurrence> def = occ.getUse_def();
					for (NameOccurrence o : def) {
						DepGraphNode g2 = g.addChild(o);
						dfs(o, g2, cond, depth);
					}
				}

				
				
				if (!occ.getLocation().getCurrentVexNode().toString().contains("switch")) {

					VexNode vexNode3 = getSwitchVexNode(occ);
	
					if (vexNode3 != null) {
						//add by lsc 2018/12/28 判断目前变量是否位于switch语句块内
						Graph graph11 = vexNode3.getGraph();
						System.out.println("100000");
						System.out.println(graph11);
						System.out.println(occ.getLocation().getCurrentVexNode());
						

						
						List<NameOccurrence> nameOccurrences = vexNode3.getOccurrences();
						System.out.println(nameOccurrences + "switch");

						// 将switch条件约束考虑进来，对其进行溯源处理
						for (NameOccurrence cNameOccurrence : nameOccurrences) {
							DepGraphNode g2 = g.addChild(cNameOccurrence);
							dfs(cNameOccurrence, g2, cond, depth + 1);
						}

						// add by lsc 2018/12/7
						// 考虑将switch内所有路径包含进来(但是要满足节点变量的image ==
						// occ.image)，这样应该更合理一些，可以跟老师探讨。
						Graph graph = vexNode3.getGraph();
						System.out.println(graph + "lsc" + occ);

						// 用于记录switch case的开始节点和终止节点
						int start = 0, end = 0;

						for (VexNode cVexNode : graph.getAllnodes()) {

							if (cVexNode.toString().contains("switch_head")) {
								start = cVexNode.getSnumber();
							}
							if (cVexNode.toString().contains("switch_out")) {
								end = cVexNode.getSnumber();
							}
						}

						for (VexNode cVexNode : graph.getAllnodes()) {

							int num = cVexNode.getSnumber();
							if (cVexNode.toString().contains("stmt") && num > start && num < end) {
								for (NameOccurrence cNameOccurrence : cVexNode.getOccurrences()) {
									if (cNameOccurrence.toString().split(":")[0].equals(occ.toString().split(":")[0])) {
										DepGraphNode g2 = g.addChild(cNameOccurrence);
										dfs(cNameOccurrence, g2, cond, depth + 1);
									}
								}
							}
						}

					}
					// add by lsc 2018/12/6晚
					// ，将顺序执行的程序放到了else分支中,这种情况的溯源定义再跟老师探讨一下
					// 若变量能追溯到switch内，则不计算switch内传播，只计算switch之下的以及switch条件约束变量之上的(包含)
					else {

						// 将所有的终结符定义前的定义删除，即若int b = a; b ++ ; b = 2 ; n = b;
						// 此时只需要分析到b=2即可
						List<NameOccurrence> def1 = occ.getUse_def();
						Collections.sort(def1, new Comparator<NameOccurrence>() {
							@Override
							public int compare(NameOccurrence o1, NameOccurrence o2) {
								int b = Integer.parseInt(o1.toString().split(":")[1]);
								int a = Integer.parseInt(o2.toString().split(":")[1]);
								return a > b ? 1 : (a == b ? 0 : -1);
							}
						});
						// 获得可以到达本使用出现的所有定义出现
						List<NameOccurrence> def = new ArrayList<>();
						for (NameOccurrence nameOccurrence : def1) {
							def.add(nameOccurrence);
							SimpleNode simpleNode = (SimpleNode) nameOccurrence.getLocation().jjtGetParent();
							
							System.err.println(nameOccurrence+"2018/12/12"+simpleNode.getOperators());
						
							boolean f1 = isDefOfConstant(nameOccurrence);
							int count = simpleNode.jjtGetNumChildren();
							boolean f2 = simpleNode.jjtGetNumChildren() == 1;
							
							
							if(simpleNode.jjtGetNumChildren() != 1) {
								List<NameOccurrence>def2 = nameOccurrence.getUndef_def();
								if(def2 != null) {
									for(NameOccurrence o : def2) {
										DepGraphNode g2 = g.addChild(o);
										dfs(o, g2, cond, depth + 1);
									}
								}
							}
							
							if (isDefOfConstant(nameOccurrence) ) {
								break;
							}
						}

						//
						for (NameOccurrence o : def) {

							DepGraphNode g2 = g.addChild(o);

							VexNode from = o.getLocation().getCurrentVexNode();
							VexNode to = occ.getLocation().getCurrentVexNode();
							List<VexNode> pList = Graph.findAPath(from, to);
							
							
							System.out.println(o+"   "+occ);
							System.out.println(pList+"????????????????????????????????");
							

							// add by lsc 2018/9/25处理条件分支
							// 为什么pList.size-1 ?
							for (int i = 0; i < pList.size(); i++) {

								VexNode a = pList.get(i);

								// add test by lsc,接下来可以以此为突破口处理if-else分支
								// System.out.println("test2018/10/9:"+a.toString()
								// +a.getOccurrences().toString());

								if (a.toString().contains("if_head")) {
									for (VexNode nVexNode : pList) {
										ValueSet valueSet = vexNode.getLastvalueset();
										System.out.println(valueSet);
										SymbolDomainSet symbolDomainSet = vexNode.getLastsymboldomainset();
										System.out.println(symbolDomainSet);
										// System.out.println(nVexNode.falsetag
										// +
										// "*******************" + nVexNode);
									}
									System.out.println("vexNode: " + a);

									SimpleNode simpleNode = a.getTreenode();
									System.out.println(simpleNode + ":" + simpleNode.getImage() + " 开始行："
											+ simpleNode.getBeginLine() + " 结束行" + simpleNode.getEndLine());

									System.out.println("USE++++++++++++++++++++++++++++++++++++++" + o + " to " + occ
											+ "   目前变量" + ": " + occ + "的use_def:" + occ.getUse_def());
									System.out.println("此节点的变量：" + a.getOccurrences() + " 此节点变量的use_def "
											+ a.getOccurrences().get(0).getUse_def());
									for (NameOccurrence o1 : a.getOccurrences()) {
										DepGraphNode g3 = g.addChild(o1);
										dfs(o1, g3, 1, depth + 1);
									}
								}
							}

							dfs(o, g2, cond, depth + 1);
						}

					}

				}

				// if (def == null || def.size() == 0) {
				// // 无定义点，尝试找全局
				// Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
				// // 获得图
				// String funcname = cfgmap2.get(cfg); // 获取当前变量所在函数的函数名
				//
				// InterCallGraph callGraph = InterCallGraph.getInstance();
				//
				// MethodNode curMNode = null;
				// for (MethodNode mn : callGraph.getINTERMETHOD()) {
				// Method m = mn.getMethod();
				// if (m.getName().equals(funcname)) {
				// curMNode = mn;
				// break;
				// }
				// }
				//
				// // add by lsc 2018/10/24
				// System.out.println("curMNode: " + curMNode.getMethod() + " "
				// + "变量名字： " + occ.toString()
				// + " " + "变量类型： " + occ.getOccurrenceType());
				//
				// if (curMNode != null) {
				// Map<Position, ArrayList<SCVPString>> callerInfo =
				// curMNode.getMethod().getCallerInfo();
				// if (callerInfo == null || callerInfo.size() == 0) {
				// List<Method> callers = new ArrayList<>();// curMNode的调用者
				// for (MethodNode mn : callGraph.getINTERMETHOD()) {
				// for (MethodNode mn2 : mn.getCalls()) {
				// if (mn2 == curMNode) {
				// callers.add(mn.getMethod());
				// }
				// }
				// }
				//
				// for (Method caller : callers) {
				// Map<String, List<SCVPString>> ext =
				// caller.getExternalEffects();
				// for (String occstr : ext.keySet()) {
				// SCVPString value = ext.get(occstr).get(0);// 假设只有1个
				// String occName = occ.toString().split(":")[0];
				// String occName1 = occstr.split(":")[0];
				// if (occName.equals(occName1)) {
				// String fileName = value.getPosition().getfileName();
				// String funcName = value.getPosition().getFunctionName();
				// String symbolName = occName1;
				// int line2 = Integer.valueOf(occstr.split(":")[1]);
				// NameOccurrence next = locate(fileName, funcName, symbolName,
				// line2);
				// if (next != null) {
				// DepGraphNode g4 = g.addChild(next);
				// dfs(next, g4, cond, depth + 1);
				// }
				// }
				// }
				// }
				// } else {
				// for (List<SCVPString> val : callerInfo.values()) {
				// SCVPString scvp = val.get(0);
				// for (String nextocc : scvp.getOccs()) {
				// String fileName = scvp.getPosition().getfileName();
				// String funcName = scvp.getPosition().getFunctionName();
				// String symbolName = nextocc.split(":")[0];
				// int line2 = Integer.valueOf(nextocc.split(":")[1]);
				// NameOccurrence next = locate(fileName, funcName, symbolName,
				// line2);
				// if (next != null) {
				// DepGraphNode g5 = g.addChild(next);
				// dfs(next, g5, cond, depth + 1);
				// }
				// }
				// }
				// }
				// }
				//
				// }
			} else if (occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE) { // 使用后定义
																					// i++
																					// ,i+=2等

				// add by lsc 2018/11/23
				SimpleNode node = occ.getLocation();
				List<NameOccurrence> def = new ArrayList<>();
				if (occ.isSelfAssignment()) {
					List<NameOccurrence> def1 = occ.getUse_def();
					for (NameOccurrence occurrence : def1) {
						def.addAll(occurrence.getUndef_def());
					}
					if (def.size() == 0) {
						System.out.println("]]]]]]]]]]]]]]]]]]]]]]]]]]]" + occ.toString());
					}
				} else {
					def = occ.getUse_def();
				}

				for (NameOccurrence o : def) {
					DepGraphNode g2 = g.addChild(o);
					//
					// VexNode from = o.getLocation().getCurrentVexNode();
					// VexNode to = occ.getLocation().getCurrentVexNode();
					// List<VexNode> pList = Graph.findAPath(from, to);
					// for (int i = 0; i < pList.size(); i++) {
					// VexNode a = pList.get(i);
					// if (a.toString().contains("if_head")) {
					// System.out.println("DEF_AFTER_USE++++++++++++++++++++++++++++++++++++++++++");
					// for (NameOccurrence o1 : a.getOccurrences()) {
					// DepGraphNode g3 = g.addChild(o1);
					// dfs(o1, g3, 1, depth + 1);
					// }
					// }
					// }
					//
					dfs(o, g2, cond, depth + 1);
				}
			} else if (occ.getOccurrenceType() == OccurrenceType.DEF) {

				// add by lsc 2018/11/23 解决了a = a + 1;不能继续向前溯源定义的问题
				if (occ.isAssignSameVar(occ.getLocation())) {

					// 这部分 解决了a = a + 1;不能继续向前溯源定义的问题
					List<NameOccurrence> def = occ.getUndef_def();

					for (NameOccurrence o : def) {
						DepGraphNode g2 = g.addChild(o);

						dfs(o, g2, cond, depth + 1);
					}

					// add by lsc 2018/12/4 这部分解决了b = b + a问题，即解决了右面变量a的继续溯源

					VexNode vexNode2 = occ.getLocation().getCurrentVexNode();
					for (NameOccurrence nameOccurrence : vexNode2.getOccurrences()) {
						if (nameOccurrence.getImage() != occ.getImage()) {
							DepGraphNode g2 = g.addChild(nameOccurrence);
							dfs(nameOccurrence, g2, cond, depth + 1);
						}
					}

				} else {

					// add by lsc 2018/11/25解决了 a += 2等问题
					if (isSelfAssignmentChange(occ, list_operator)) {

						List<NameOccurrence> def = occ.getUndef_def();

						for (NameOccurrence o : def) {
							DepGraphNode g2 = g.addChild(o);
							//
							// VexNode from =
							// o.getLocation().getCurrentVexNode();
							// VexNode to =
							// occ.getLocation().getCurrentVexNode();
							// List<VexNode> pList = Graph.findAPath(from, to);
							// for (int i = 0; i < pList.size(); i++) {
							// VexNode a = pList.get(i);
							// if (a.toString().contains("if_head")) {
							// System.out.println("DEF2++++++++++++++++++++++++++++++++++++++");
							// for (NameOccurrence o1 : a.getOccurrences()) {
							// DepGraphNode g3 = g.addChild(o1);
							// dfs(o1, g3, 1, depth + 1);
							// }
							// }
							// }
							//
							dfs(o, g2, cond, depth + 1);
						}
					}

					
					
					
					SCVPString scvp = occ.getSCVP();
					List<String> vlist = scvp.getOccs();
					
//					//add by lsc 2018/12/11,为了解决数组问题,尚未解决
//					if(vlist.isEmpty()) {
//						VexNode cVexNode = occ.getLocation().getCurrentVexNode();
//						System.err.println(cVexNode.getOccurrences()+"lsclsc");
//						System.err.println(occ.getLocation()+" "+ occ);
//						
//						//取得右侧变量名列表，这个get函数被修改了，pri->post,适时改回来
//						List rightVars = getRightVar(occ.getLocation());
//						System.out.println(rightVars.toString()+"pppppppppppp");
//						
//						for(Object o:rightVars)
//			    		{
//			    			if(o instanceof ASTPostfixExpression)
//			    			{
//			    				ASTPostfixExpression priExp=(ASTPostfixExpression) o;
//			    			
//			    				
//			    				ASTFunctionDefinition astFunctionDefinition = (ASTFunctionDefinition) priExp.getFirstParentOfType(ASTFunctionDefinition.class);
//			    				String funcName = astFunctionDefinition.getImage();
//			    				
//			    				System.out.println(args[1]+" "+funcName+" " +priExp.getImage()+"  "+priExp.getBeginLine()+"lsc");
//			    				
//			    				NameOccurrence nameOccurrence = locate(args[1], funcName, priExp.getImage(), priExp.getBeginLine());
//			    				System.out.println(nameOccurrence + " this");;
//			    				DepGraphNode g2 = g.addChild(nameOccurrence);
//								dfs(nameOccurrence, g2, cond, depth + 1);
//			    			}
//			    		}
//						
//						
//
//					}
					

					// add test by lsc 2018/10/9
					System.out.println("test2018/10:" + vlist.toString());

					for (String v : vlist) {
						Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
						NameOccurrence o = cfg.getOcctable().get(v);
						if (o.getImage().toString().equals(occ.getImage()))
							continue;
						DepGraphNode g2 = g.addChild(o);
						//
						// VexNode from = o.getLocation().getCurrentVexNode();
						// VexNode to = occ.getLocation().getCurrentVexNode();
						// List<VexNode> pList = Graph.findAPath(from, to);
						// for (int i = 0; i < pList.size(); i++) {
						// VexNode a = pList.get(i);
						// if (a.toString().contains("if_head")) {
						// System.out.println("DEF3++++++++++++++++++++++++++++++++++++++");
						// for (NameOccurrence o1 : a.getOccurrences()) {
						// DepGraphNode g3 = g.addChild(o1);
						// // if (cond==0) {
						// // cond=1;
						// // System.out.println(o + "," + g);
						// // }
						// dfs(o1, g3, 1, depth + 1);
						// }
						// }
						// }
						//
						dfs(o, g2, cond, depth + 1);
					}
					String s = scvp.getStructure();

					System.out.println("s" + s + "==============================================================");
					if (s.contains("Function:")) { // 返回值
						int id = s.indexOf("Function");
						s = s.substring(id);
						String[] fs = s.trim().split("Function:");

						for (String string : fs)
							System.out.println("函数名称：" + string
									+ "==============================================================");

						ASTStatement statement = (ASTStatement) occ.getLocation()
								.getFirstParentOfType(ASTStatement.class);

						System.out.println("statement:" + statement
								+ "==============================================================");

						List<Node> priList = statement.findChildrenOfType(ASTPrimaryExpression.class);
						System.out.println(
								"priList" + priList + "==============================================================");
						for (String f : fs) {
							for (Node n : priList) {
								ASTPrimaryExpression pri = (ASTPrimaryExpression) n;
								if (pri.isMethod() && pri.getImage().equals(f)) {
									// 2011.6.24
									// 目前尚未解决的问题：如果是函数指针形式的函数调用，如何获取正确的函数调用？

									System.out.println(pri.getMethodDecl()
											+ "==============================================================");
									if (pri.getMethodDecl() == null)
										continue;
									Method m = pri.getMethodDecl().getMethod();
									System.out.println("Method:" + m
											+ "==============================================================");
									SimpleNode entNode = pri.getMethodDecl().getMethodNameDeclaratorNode();
									System.out.println("entNode: " + entNode
											+ "==============================================================");
//									Graph cfg = null;
//									if (entNode instanceof ASTFunctionDefinition)
//										cfg = ((ASTFunctionDefinition) entNode).getGraph();
									
									//add by lsc 2019/1/2
									entNode = map_function_simpleNode.get(f);
									Graph cfg = null;
									if (entNode instanceof ASTFunctionDefinition)
										cfg = ((ASTFunctionDefinition) entNode).getGraph();
									
									List<SCVPString> ret = m.getReturnList();
									System.out.println("m.getReturnList:" + ret.toString()
											+ "==============================================================");
									for (SCVPString scvpString : ret) {
										for (String v : scvpString.getOccs()) {
											if (cfg != null) {
												NameOccurrence o = cfg.occtable.get(v);
												System.err.println(scvpString+"}}}}"+o.toString()+occ);
												DepGraphNode g2 = g.addChild(o);
												dfs(o, g2, cond, depth + 1);
											}
										}
									}
								}
							}
						}
					}
				}

			} 	else if(occ.getOccurrenceType() == OccurrenceType.ENTRANCE) {
				//获得方法定义点的语法树节点,(之后可以间接获取方法名等相关信息)
				ASTFunctionDefinition funcdef = (ASTFunctionDefinition) occ.getLocation().getFirstParentOfType(ASTFunctionDefinition.class);
				
				//add test by lsc 2018/11/26
				//解决了参数索引不正确的问题，原来参数索引获取方式存在问题(不能保证funcdef.getScope()的参数逆序，新的代码依赖抽象语法树，保证正确).
				String[] ParameterList = new String[funcdef.getParameterCount()];
				int count = 0;
//				if(occ.toString().split(":")[1].equals("211")){
					System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
					System.out.println(funcdef.getImage());
//					ASTParameterList astParameterList = (ASTParameterList) funcdef.findChildrenOfType(ASTParameterList.class);
					List<SimpleNode> list = funcdef.findXpath(".//ParameterDeclaration");
					for(SimpleNode simpleNode : list) {
						List<SimpleNode>list2 = simpleNode.findXpath(".//Declarator");
						for(SimpleNode simpleNode2 : list2){
							System.out.println(simpleNode2.getImage()+":"+simpleNode2.getBeginLine());
							ParameterList[count ++] = simpleNode2.getImage();
						}
					}
					
			
					System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
//				}
				
				
//				System.out.println("参数个数 :"+funcdef.getParameterCount()+"    行号： "+ occ.toString().split(":")[1]); //获取这一行的参数个数
//				
//			
//				//可以得到lsc:MethodScope(null): (variables:d < int >,n < int >,m < int >)，注意参数顺序逆序
//				System.out.println("lsc:"+funcdef.getScope());         
//				
//				String string = funcdef.getScope().toString().split("variables:")[1];
//				string = string.substring(0 ,string.length() - 1);
//				System.out.println(string);
//				
//				String[] strings = string.split(",");
//				for(int i = 0 ; i < strings.length ; i ++) {
//					strings[i] = strings[i].split(" <")[0];
//					System.out.println(strings[i]);
//				}
				
				int index = 0 ;
//				boolean isFind = false;       //判断是否找到
				
				System.out.println("当前参数"+occ.toString().split(":")[0]);
//				
//				for(int i = strings.length - 1 ; i >= 0 ; i --) {
//				
//					index ++;
//					if(occ.toString().split(":")[0].equals(strings[i]))
//					{
////						isFind = true;
//						break;
//					}
//			
//				}
				
				for(int i = 0 ; i < count ; i ++) {
					if(occ.toString().split(":")[0].equals(ParameterList[i])) {
						index = i + 1;
						break;
					}
				}
				
				
				System.out.println("得出此变量："+occ.toString().split(":")[0]+"的index为:" + index);
				
//				add test by lsc 2018/9/27
//				System.out.println("当前参数："+occ.toString());
//				System.out.println();
//				
//				VexNode vexNode1 = occ.getLocation().getCurrentVexNode();      //获取当前变量所在的节点
//	            
//				
//				int index = 1;
//				
//				for(NameOccurrence nameOccurrence : vis) {
//					System.out.println(nameOccurrence.toString());
					
//					if(Integer.parseInt(occ.toString().split(":")[1]) == Integer.parseInt(nameOccurrence.toString().split(":")[1])){
//						System.out.println("当前行号:"+Integer.parseInt(nameOccurrence.toString().split(":")[1]));
//						System.out.println("当前变量:"+nameOccurrence.toString().split(":")[0]);
//						index ++ ;
//						if(nameOccurrence.toString().split(":")[0].equals(occ.toString().split(":")[0])){
//							System.out.println("index:"+index);
//							break;
//						}
//					}
					
//				}
			
				
				if(funcdef!=null) {
					
					String funNameString = funcdef.getImage();
					List<String> listfuncList = map_function.get(funNameString);
					System.out.println(funcdef + "  " + map_function.get(funNameString));
					
					for(String string : listfuncList) {
			
						
						System.out.println(map_function_simpleNode.get(string));
						SimpleNode astFunctionDeclaration =  map_function_simpleNode.get(string);
				
						
						List<SimpleNode> listnodeList = astFunctionDeclaration.findXpath(".//PrimaryExpression[@Method='true']");
						
						for(SimpleNode node : listnodeList) {
							if(node.getImage().equals(funNameString)) {
								String fileName = map_function_path.get(string);
								String funcName = string;
								ASTPostfixExpression astPostfixExpression = (ASTPostfixExpression) node.jjtGetParent();
								System.out.println("父节点是:" +astPostfixExpression);
								List<SimpleNode> nodes = astPostfixExpression.findXpath(".//PrimaryExpression[@Method='false']");
								String symbolName = nodes.get(index - 1).getImage();
								int line1 = node.getBeginLine();
								NameOccurrence occ2 = locate(fileName, funcName, symbolName, line1);
								System.out.println("occ2内容："+ occ.toString());
								
								if (occ2 == null)
									continue;
								DepGraphNode g3 = g.addChild(occ2);
								dfs(occ2, g3, cond, depth+1);
							}
						}
						
						
						
					}
					
//					//用一个HashMap来记录前置摘要，来处理被调用函数参数问题，即参数向上溯源问题
//					//我觉得需要添加一个参数的索引index，用于区分到达溯源哪个参数 2018/9/27 lsc
//					HashMap<Position, ArrayList<SCVPString>> callerInfo = funcdef.getDecl().getMethod().getCallerInfo();
//					System.out.println("today 映射： "+ callerInfo);
//					
//					for(Position p : callerInfo.keySet()) {
//						//add by lsc 2018/9/27
//						
////						System.out.println("test:" + index);
//						
////						System.out.println("test："+p.toString());
////						System.out.println("scvpstring :" + callerInfo.get(p).toString());
//						
//						Graph cfg = cfgmap.get(p.getFunctionName());
//						if(cfg!=null) {
//							for(SCVPString scvp : callerInfo.get(p)) {
//								
//								String fileName = p.getFileName();
//								String funcName = p.getFunctionName();
//								String symbolName = scvp.getVar();
//					
//						
//								
//								//add test by lsc
//								System.out.println("test:"+symbolName);
//								System.out.println("index:"+p.getIndex());
//								int line1 = p.getBeginLine(); 
//							   
//								
//								//用于对比参数索引进行精确溯源 add by lsc 2018/10/9
//								if(p.getIndex() == index){
//									 System.out.println("行号:"+line1 +"  变量： "+symbolName+"  索引："+index);
//								NameOccurrence occ2 = locate(fileName, funcName, symbolName, line1);
//								System.out.println("occ2内容："+ occ.toString());
//								
//								if (occ2 == null)
//									continue;
//								DepGraphNode g3 = g.addChild(occ2);
//								dfs(occ2, g3, cond, depth+1);
//					
//								
//								for(String v:scvp.getOccs()) {
//									
//									System.out.println(scvp.getOccs()+"lsc");
//									
//									NameOccurrence o = cfg.occtable.get(v);
//									DepGraphNode g2 = g.addChild(o);
//									dfs(o, g2,cond, depth+1);
//								}
//								
//								}
//								
//								
//							}
//						}
//					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

	
	 /**
     * add by lsc 2018/12/7晚，为了判断数组变量是否位于等号左侧
     * @return 判断当前变量出现（NameOccurence)是否位于＝左侧，即是否为变量赋值DEF
     */
    public boolean isOnLeftHandSideForArray(NameOccurrence occ) {
    	SimpleNode declarator=null;
       
        if (occ.getLocation() instanceof ASTPostfixExpression ) {
        	Node assignment=occ.getLocation().jjtGetParent().jjtGetParent();
        	if(assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren()==3){
        		return true;
        	}
        } 
        if(occ.getLocation().jjtGetParent() instanceof ASTPostfixExpression)
        {
        	declarator = (ASTPostfixExpression) occ.getLocation().jjtGetParent();
        	Node assignment=declarator.jjtGetParent().jjtGetParent();
        	if(assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren()==3){
        		return true;
        	}
        	//add else branch by cmershen,2016.5.31 添加对*p=2类型的支持
        	else 
        	{
        		Node child = assignment;
        		assignment = assignment.jjtGetParent();
        		if(assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren()==3 && child == assignment.jjtGetChild(0)){
            		return true;
            	}
        	}
        }
        return false;
    }
	
	
	
	/*
	 * add by lsc 2018/12/4 , 取得等号右边的变量名列表
	 */
	public List getRightVar(SimpleNode node) {
		Node assignmentNode = node.getFirstParentOfType(ASTAssignmentExpression.class);
		if (assignmentNode != null && assignmentNode instanceof ASTAssignmentExpression
				&& assignmentNode.jjtGetNumChildren() == 3) {

			ASTAssignmentExpression rightExpr = (ASTAssignmentExpression) assignmentNode.jjtGetChild(2);

			// 取得右侧表达式中所有的变量名列表
			List rightVars = rightExpr.findChildrenOfType(ASTPrimaryExpression.class);
			return rightVars;

		}
		
		//add by lsc 2018/12/11，当直接定义的时候，例如int m = a + 1;
		if(node instanceof ASTDirectDeclarator) {
			ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) node.getFirstParentOfType(ASTInitDeclarator.class);
			ASTInitializer astInitializer = (ASTInitializer) astInitDeclarator.getFirstChildOfType(ASTInitializer.class);
			List rightVars = astInitializer.findChildrenOfType(ASTPrimaryExpression.class);
			return rightVars;
		}
		
		return null;
	}

	/*
	 * add by lsc 2018/12/6增加了对switch的间接控制处理 add by lsc 2018/12/6
	 * 判断变量追溯是否会追溯到switch内 若能追溯进则返回switch节点(VexNode),否则返回null
	 */
	public VexNode getSwitchVexNode(NameOccurrence occ) {

		List<NameOccurrence> def_temp = occ.getUse_def();
		for (NameOccurrence cNameOccurrence : def_temp) {

			Graph graph1 = cNameOccurrence.getLocation().getCurrentVexNode().getGraph();

			for (VexNode vexNode2 : graph1.getAllnodes()) {
				if (vexNode2.toString().contains("switch_head")) {
					return vexNode2;
					// List<NameOccurrence>list = vexNode2.getOccurrences();
					// for(NameOccurrence nameOccurrence : list) {
					// for(NameOccurrence nameOccurrence2 :
					// nameOccurrence.getUse_def()) {
					// System.out.println("switch条件变量的前驱定义点所在语法树节点:"+nameOccurrence2.getLocation());
					//
					// ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator)
					// nameOccurrence2.getLocation().getFirstParentOfType(ASTInitDeclarator.class);
					// ASTPrimaryExpression astPrimaryExpression =
					// (ASTPrimaryExpression)
					// astInitDeclarator.getFirstChildInstanceofType(ASTPrimaryExpression.class);
					// System.out.println(astPrimaryExpression);
					// System.out.println(astPrimaryExpression.isLeaf());
					// if(!astPrimaryExpression.isLeaf()) {
					// ASTConstant astConstant = (ASTConstant)
					// astPrimaryExpression.getFirstDirectChildOfType(ASTConstant.class);
					// System.out.println(astConstant.getImage());
					// }
					//
					// boolean flag = isDefOfConstant(nameOccurrence2);
					// System.out.println("switch条件变量的前驱定义点是否是常量赋值： "+flag);
					// System.out.println("switch条件变量的前驱定义值："+nameOccurrence2.getSCVP());
					// }
					//
					//
					// }
				}
			}
		}
		return null;
	}
	
	
	/*
	 * add by lsc 2018/12/28 判断一个变量是否在switch语句块内部
	 */
	public boolean isInSwitch(NameOccurrence occ) {
		VexNode vexNode = occ.getLocation().getCurrentVexNode();
		List<NameOccurrence> def_temp = occ.getUse_def();
		for (NameOccurrence cNameOccurrence : def_temp) {

			Graph graph1 = cNameOccurrence.getLocation().getCurrentVexNode().getGraph();

			for (VexNode vexNode2 : graph1.getAllnodes()) {
				if (vexNode2.toString().contains("switch_head")) {
					
				}
			}
		}
		return false;
	}

	/*
	 * add by lsc 2018/11/26 判断定义点是否为常量定义
	 */
	public boolean isDefOfConstant(NameOccurrence occ) {

		ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) occ.getLocation()
				.getFirstParentOfType(ASTInitDeclarator.class);
		// motified by lsc 2018/12/6 int b = a或者 int b = 1等情况，包含int
		if (astInitDeclarator != null) {
			ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression) astInitDeclarator
					.getFirstChildInstanceofType(ASTPrimaryExpression.class);
			if (!astPrimaryExpression.isLeaf()) {
				ASTConstant astConstant = (ASTConstant) astPrimaryExpression
						.getFirstDirectChildOfType(ASTConstant.class);
				for (Character character : astConstant.getImage().toCharArray()) {
					if (!(character >= '1' && character <= '9')) {
						return false;
					}
				}
				return true;
			}
			return false;
		} else {

			ASTAssignmentExpression assignmentNode = (ASTAssignmentExpression) occ.getLocation()
					.getFirstParentOfType(ASTAssignmentExpression.class);
			if (assignmentNode != null && assignmentNode instanceof ASTAssignmentExpression
					&& assignmentNode.jjtGetNumChildren() == 3) {

				ASTAssignmentExpression rightExpr = (ASTAssignmentExpression) assignmentNode.jjtGetChild(2);

				// 取得右侧表达式中所有的变量名列表
				List rightVars = rightExpr.findChildrenOfType(ASTPrimaryExpression.class);
				for (Object o : rightVars) {
					if (o instanceof ASTPrimaryExpression) {
						ASTPrimaryExpression priExp = (ASTPrimaryExpression) o;
						if (!priExp.isLeaf()) {
							ASTConstant astConstant = (ASTConstant) priExp.getFirstDirectChildOfType(ASTConstant.class);
							for (Character character : astConstant.getImage().toCharArray()) {
								if (!(character >= '1' && character <= '9')) {
									return false;
								}
							}
						} else {
							return false;
						}
					}
				}
				return true;
			}
			return false;

		}

	}

	/*
	 * add by lsc 2018/11/24 查看该变量定义是否为 += ， -= ， *= ,/=,%=等更新
	 */
	private boolean isSelfAssignmentChange(NameOccurrence occurrence, List<String> list_operator) {
		if (!(occurrence.getOccurrenceType() == OccurrenceType.DEF
				|| occurrence.getOccurrenceType() == OccurrenceType.USE)) {
			return false;
		}
		for (String string : list_operator) {
			String str = occurrence.toString().split(":")[1];
			if (string.contains(str)) {
				if (string.contains("+=") || string.contains("-=") || string.contains("*=") || string.contains("/=")
						|| string.contains("%=")) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * add by lsc 2018/9/19 获取要求变量的NameOccurrence
	 * 
	 * @param fileName
	 * @param funcName
	 * @param symbolName
	 * @param line
	 * @return
	 */
	private NameOccurrence locate(String fileName, String funcName, String symbolName, int line) {
		Graph cfg = cfgmap.get(funcName);
		String occStr = symbolName + ":" + line;
		if (cfg == null)
			return null;
		return cfg.getOcctable().get(occStr);
	}

	/**
	 * occ; child; private List<VexNode> path; isCond;
	 * 
	 * @author lsc
	 *
	 */
	@SuppressWarnings("unused")
	private class DepGraphNode {
		private NameOccurrence occ;
		private List<DepGraphNode> child;
		private List<VexNode> path;
		private boolean isCond;

		public DepGraphNode(NameOccurrence occ) {
			this.occ = occ;
			child = new ArrayList<DepGraphNode>();
			path = new ArrayList<VexNode>();
			isCond = false;

		}

		public DepGraphNode addChild(NameOccurrence o) {
			DepGraphNode childNode = new DepGraphNode(o);
			child.add(childNode);

			try {

				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				childNode.path = Graph.findAPath(from, to);

				return childNode;
			} catch (Exception e) {
				// e.printStackTrace();
				return null;
			}
		}

	}

	/**
	 * 从函数定义节点获取调用语句节点，可以从ASTPostfixExpression.getImage()获取调用函数的函数名 add by lsc
	 * 2019/11/20
	 * 
	 * @param def
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public List<ASTPostfixExpression> getCalleeNodesFromFunction(ASTFunctionDefinition def) {
		String xpathString = ".//PostfixExpression[@Operators='(']";
		softtest.cfg.c.Graph cfg = def.getGraph();
		VexNode entryNode = cfg.getEntryNode();
		SimpleNode entry_astnode = entryNode.getTreenode();
		List<ASTPostfixExpression> xList = null;
		try {
			xList = entry_astnode.findChildNodesWithXPath(xpathString);
		} catch (JaxenException e) {
			e.printStackTrace();
		}
		return xList;
	}

	public List<List<String>> getList_Out_Valiable(Map<VexNode, List<String>> map_line_list_out_variable) {
		// 外部输入源获取
		// 添加了vexNode节点信息 2018/11/29
		for (Entry<VexNode, List<String>> entry : map_line_list_out_variable.entrySet()) {
			VexNode vexNode = entry.getKey();
			List<String> list = entry.getValue();
			list.add(vexNode.toString());
			list_out_variable.add(list);
		}
		System.out.println("输出与变量相关的外部输入源： ");
		System.out.println("list_out_variable: " + list_out_variable);

		System.out.println("输出节点与对应变量相关的外部输入源的映射：");
		System.out.println("个数： " + map_line_list_out_variable.size());
		for (Entry<VexNode, List<String>> entry : map_line_list_out_variable.entrySet()) {
			VexNode vexNode = entry.getKey();
			List<String> list = entry.getValue();
			System.out.println(vexNode + " " + list);
		}
		return list_out_variable;
	}

	public HashSet<String> analyse3() throws Exception {

		
		getpathSet3(args[2], args[2]);

		System.out.println("输出面向函数调用点计算路径输入源结果：");
		// System.out.println(pathSet3);

		// System.out.println("溯源路径函数的相关内嵌函数映射:");
		// Set<String> set = null ;
		//
		// for(String string : pathSet3) {
		// set = new HashSet<>();
		// String[] strings = string.split("<-");
		//
		// for(String string2 : strings) {
		// set.add(string2);
		// }
		// }
		//
		// for(String string : set) {
		// if(map_function_contains.containsKey(string)) {
		// map_function_internal.put(string, map_function_contains.get(string));
		// }
		// }
		//
		// //操作HightlightFunction
		// for(String string : pathSet3) {
		// Set<String> set2 = new HashSet<>();
		// String[] strings = string.split("<-");
		// for(String string2 : strings) {
		// set2.add(string2);
		// if(map_function_contains.containsKey(string2)) {
		// for(String string3 : map_function_contains.get(string2)) {
		// if(analyse2().containsKey(string3)) {
		// set2.add(string3);
		// }
		// }
		// }
		//
		// }
		// HighlightFunction.add(set2);
		// }
		//
		//
		//// for(Entry<String, List<String>> entry :
		// map_function_internal.entrySet()) {
		//// System.out.println(entry.getKey()+":" + entry.getValue());
		//// }
		//
		// System.out.println("输出HighlightFunction:");
		// for(Set<String> set2 : HighlightFunction) {
		// for(String string : set2) {
		// System.out.print(string +" ");
		// }
		// System.out.println();
		// }
		//
		return pathSet3;
	}

	public void setArgs(String[] args) {
		this.args = args;
	}

	public Map<String, Boolean> getCondLineMap() {
		return condLineMap;
	}

	public void setCondLineMap(Map<String, Boolean> condLineMap) {
		this.condLineMap = condLineMap;
	}

	//add by lsc 2018/12/24
	public HashMap<String, Graph> getCfgmap() {
		return cfgmap;
	}

	
}
