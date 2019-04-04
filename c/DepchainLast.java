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
import java.util.Stack;
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
import com.sun.jndi.cosnaming.IiopUrl.Address;
import com.sun.org.apache.bcel.internal.generic.IFGE;
import com.sun.org.apache.bcel.internal.generic.RETURN;
import com.sun.org.apache.bcel.internal.generic.VariableLengthInstruction;
import com.sun.org.apache.xml.internal.resolver.helpers.PublicId;
import com.sun.swing.internal.plaf.basic.resources.basic;
import com.sun.tracing.dtrace.ArgsAttributes;
import com.sun.tracing.dtrace.FunctionName;
import com.sun.xml.internal.bind.v2.model.core.ID;
import com.sun.xml.internal.bind.v2.runtime.Name;
import com.sun.xml.internal.ws.message.StringHeader;

import edu.emory.mathcs.backport.java.util.Arrays;
import softtest.CharacteristicExtract.c.Graph_Info;
import softtest.CharacteristicExtract.c.StatementFeature;
import softtest.CharacteristicExtract.c.test;
import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTFieldId;
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
import softtest.test.c.hangtiancheng.STBO;
import sun.java2d.pipe.SpanShapeRenderer.Simple;
import sun.net.www.content.text.plain;

public class DepchainLast implements Serializable {
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

	public DepchainLast(String[] args) {

		// add by lsc 2018/9/20
		// 此处为分析路径下的文件，args[0]表示分析路径下的所有.c文件，args[1]表示分析指定的.c文件
		this.analysisDir = args[0];
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

	// add by lsc 2019/1/2
	public List<String> list_outsource = new ArrayList<String>();

	public static void main(String[] args) throws Exception {
		DepchainLast test = new DepchainLast(args);
		// motified by lsc 2018/11/29，无论参数如何，先将外部输入源获取
		// add by lsc 2018/11/12记录外部输入源
		System.out.println(test.analyse1());
		// add by lsc 2019/1/2为了获取相关准备信息

		if (args.length == 5) {

			System.out.println(test.analyse2());// 输入域分析

		
			test.analyse3();
			System.out.println("pathSet3: " + test.pathSet3);

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
			for (Map.Entry<String, List<String>> entry : test.map_function_internal.entrySet()) {
				System.out.println(entry.getKey() + ":" + entry.getValue());
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

	}

	/*
	 * add by lsc 2019/1/2 获取相应结果
	 */
	public void prepare() throws Exception {
		SearchFunction searchFunction = new SearchFunction();
		searchFunction.main(args);
		list_function = searchFunction.getList();
		// System.out.println(list_function.toString());
		map_function = searchFunction.getMapOfFunction();
		map_function_contains = searchFunction.getMapOfFunctionContains();
		// add by lsc 2019/1/2
		map_function_path = searchFunction.getMap_Function_Path();
		map_function_simpleNode = searchFunction.getMap_Function_SimpleNode();

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
		// args1[0] = args[1];
		tg.main(args);
		list_out = tg.getList();
		list_outsource = tg.getlist_outsource();
		return list_out;
	}

	public List<String> getList_outSource() throws Exception {
		test_outputlib tg = new test_outputlib();

		tg.main(args);

		list_outsource = tg.getlist_outsource();
		return list_outsource;
	}

	// 全局变量map2中存储有每个函数中相关溯源点的行号
	private Map<String, Set<Integer>> map2 = new HashMap<>();

	 List<List<VexNode>> path100 = new ArrayList<>();
	List<String> paths = new ArrayList<>();

	public Map<String, Set<Integer>> analyse2() throws Exception {
		findAstOfVariable findAstOfVariable = new findAstOfVariable();
		findAstOfVariable.main(args);
		list_operator = findAstOfVariable.getList_Operator();

		System.out.println(list_operator.toString());
		prepare();
		process();


		// add by lsc 2019/1/11
		String funcName = args[2];
		String varName = args[3];
		int line = Integer.parseInt(args[4]);
		VexNode vexNode = getVexNodeOflocate(funcName, varName, line);
	   

		// 测每个节点的前驱节点
		getVexNodeOfPreMap(vexNode);


		set_path_node.clear();
		paths.clear();
		paths = getAllPath(vexNode, paths);
		System.err.println("paths : ");
		Set<String> set = new HashSet<>();
		for (String str : paths) {
			set.add(str);
			System.out.println(str);
		}
		System.err.println("set_path_node: " + set_path_node.toString());
		System.err.println("paths中元素个数为: " + paths.size());
		System.err.println("set中元素个数为: " + set.size());

		//节点解析分析
		String string = paths.get(0);
		List<String> list = new ArrayList<>();
		list.add(args[2]);
		vexnode_Analysis(string , list);

		// generate2(occ);
		//
		// System.out.println(vis.toString());
		// System.out.println("信号量追踪情况：" + VariableOfSort.toString());
		//
		// System.out.println("map2:");
		return map2;
	}
	
    public Map<String, Set<Integer>> vexnode_Analysis(String string , List<String> list) {
    
    	
    	return map2;
    }

	// public HashSet<String> pathSet = new HashSet<String>();
	// 应费克雄要求，将调用路径关系不以String类型存储以LinkedList方式存储
	public HashSet<String> pathSet = new HashSet<>();
	public LinkedList<String> linkedList = new LinkedList<>();
	
	


	private Map<String, Set<String>> vexMap = new HashMap<>();
	private Map<String, Boolean> condMap = new HashMap<>();
	private Map<String, Boolean> condLineMap = new HashMap<>();


	private HashSet<NameOccurrence> vis = new HashSet<>();

	// add by lsc 2018/11/28晚，为了追踪信号量的分析情况
	private List<NameOccurrence> VariableOfSort = new ArrayList<>();

	/*
	 * add by lsc 2019/1/12 根据当前控制流节点得到当前控制流图上节点名称与节点的map映射
	 */
	public Map<String, VexNode> getMapOfVexNode(VexNode vexNode) {
		Map<String, VexNode> map = new HashMap<>();
		Graph graph = vexNode.getGraph();
		for (VexNode nodes : graph.getAllnodes()) {
			if (!map.containsKey(nodes.toString())) {
				map.put(nodes.toString(), nodes);
			}
		}
		return map;
	}
	
	/*
	 * add by lsc 2019/1/22 根据当前函数得到当前控制流图上节点名称与节点的map映射
	 */
	public Map<String, VexNode> getMapOfVexNode(String funcName) {
		Map<String, VexNode> map = new HashMap<>();
		Graph graph = cfgmap.get(funcName);
		for (VexNode nodes : graph.getAllnodes()) {
			if (!map.containsKey(nodes.toString())) {
				map.put(nodes.toString(), nodes);
			}
		}
		return map;
	}

	/*
	 * add by lsc 2019/1/12 判断两个节点是否相连接
	 */
	public boolean IsConnect(VexNode head, VexNode tail) {
		Hashtable<String, Edge> hashtable = head.getInedges();
		Set<String> set = hashtable.keySet();
		for (String string : set) {
			Edge edge = hashtable.get(string);
			VexNode node = edge.getTailNode();
			if (node.equals(tail)) {
				return true;
			}
		}
		return false;
	}

	
	/*
	 * add by lsc 2019/13/11:46 目的：为了测试用 功能：根据给定的任意一个控制流图节点获取当前控制流上所有节点与前驱节点的映射
	 */
	public Map<VexNode, List<VexNode>> getVexNodeOfPreMap(VexNode vexNode) {
		Graph graph = vexNode.getGraph();
		Map<VexNode, List<VexNode>> map = new HashMap<>();
		for (VexNode node : graph.getAllnodes()) {
			Hashtable<String, Edge> hashtable = node.getInedges();
			Set<String> set = hashtable.keySet();
			List<VexNode> list = new ArrayList<>();
			for (String string : set) {
				Edge edge = hashtable.get(string);
				VexNode vexNode2 = edge.getTailNode();
				list.add(vexNode2);
			}
			if (!map.containsKey(node)) {
				map.put(node, list);
			}
			System.out.println("节点和其前驱节点的映射：" + node + "   :    " + list +"     :    " + node.getTreenode() +"    :    "+getVexNodeType(node));
		}
		return map;
	}

	// add by lsc 2019/1/15用来存储已经被访问过的节点
	Set<VexNode> set_path_node = new HashSet<>();

	
	
	
	/*add by lsc 2019/1/16
	 * 参数两个 ，目标节点参数，当前路径
	 *功能：根据目标节点获取从函数入口到其的所有可达路径
	 */
	public List<String> getAllPath(VexNode vexNode , List<String> path) {
		if (path.isEmpty()) {
		findpath("", vexNode);
		}
		return path;
	}
	
	/*
	 * add by lsc 2019/1/16 晚20:32
	 */
	public void findpath(String oldpath , VexNode newVexNode ) {
		if(!oldpath.contains(newVexNode.toString())) {
			oldpath = oldpath +"<-" + newVexNode.toString();
			set_path_node.add(newVexNode);
		}
		Hashtable<String, Edge> hashtable = newVexNode.getInedges();
		if(hashtable.isEmpty()) {
			paths.add(oldpath);
		}
		else {
			Set<String> set = hashtable.keySet();
			for(String string : set) {
				Edge edge = hashtable.get(string);
				VexNode vexNode = edge.getTailNode();
				if(!set_path_node.contains(vexNode) || !oldpath.contains(vexNode.toString())) {
					findpath(oldpath, vexNode);
				}
				else if(set_path_node.contains(vexNode) && oldpath.contains(vexNode.toString())) {
					if(vexNode.toString().contains("for_head") || vexNode.toString().contains("while_head")) {
						oldpath = oldpath + "<-" + vexNode.toString();
						Hashtable<String, Edge> table = vexNode.getInedges();
						Set<String>set_table = table.keySet();
						for(String string2 : set_table) {
							Edge edge2 = table.get(string2);
							VexNode vexNode2 = edge2.getTailNode();
							if(vexNode2.getSnumber() < vexNode.getSnumber()) {
								findpath(oldpath, vexNode2);
							}
						}
					}
				}
			}
		}
	}
	
	
	
	

	/*
	 * add by lsc 2019/1/16
	 * 将一个set集合中的内容进行逆序排序，输出一个数组集合
	 */
	public String[] set_to_array_sort(Set<String> set) {
		String[] array = new String[set.size()];
		int count = 0;
		for(String string : set) {
			array[count++] = string;
		}
		Arrays.sort(array);
		return array;
	}
	
	
	/*
	 * add by lsc 2019/1/16
	 * 计算一个路基字符串中包含特定节点名字几次
	 */
	public int get_vexnode_count(String str , VexNode vexNode) {
		int count = 0;
		String[] strings = str.split("<-");
		for(String string : strings) {
			if(string.equals(vexNode.toString())) {
				count ++;
			}
		}
		return count;
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

	




	public HashSet<String> analyse3() throws Exception {

		getpathSet3(args[2], args[2]);

		System.out.println("输出面向函数调用点计算路径输入源结果：");

		return pathSet3;
	}

	public void setArgs(String[] args) {
		this.args = args;
	}



	// add by lsc 2018/12/24
	public HashMap<String, Graph> getCfgmap() {
		return cfgmap;
	}

	/*
	 * add by lsc 2019/1/10 由函数名，变量名，行号获取定位点的控制流图节点
	 */
	public VexNode getVexNodeOflocate(String funcName, String varName, int line) {
		SimpleNode simpleNode = map_function_simpleNode.get(funcName);
		Graph graph = cfgmap.get(funcName);
		for (VexNode vexNode : graph.getAllnodes()) {
			SimpleNode temp = vexNode.getTreenode();
			if (temp.getBeginLine() == line) {
				return vexNode;
			}
		}
		return null;
	}

	/*
	 * add by lsc 2019/1/10 由函数名，变量名，变量名的索引（即第几个变量名)，行号获取定位点的抽象语法树结点
	 */
	public SimpleNode getSimpleNodeOflocate(String funcName, int index, String varName, int line) {
		SimpleNode node = null;
		VexNode vexNode = getVexNodeOflocate(funcName, varName, line);
		SimpleNode simpleNode = vexNode.getTreenode();
		List<SimpleNode> list = null;
		if (varName.contains(".") || varName.contains("->") || varName.contains("[")) {
			list = simpleNode.findXpath(".//PostfixExpression");
		} else {
			list = simpleNode.findXpath(".//PrimaryExpression");
		}
		return list.get(index - 1);
	}
	
	
	/*
	 *add by lsc 2019/1/21
	 *对控制流节点类型进行判断
	 *type == 0 控制流图入口节点
	 *type == 1 只有函数 f()或者f(c)
	 *type == 2.1 有定义声明 ： 例如 int c = m + f();
	 *type == 2.2有定义声明(仅仅声明，未赋值) , 例如int c;
	 *type == 3 无定义声明 ： 例如 c = m + a;
	 *type == 4 控制流图出口节点
	 *type == 5 库函数
	 *type == 6 其他情况 比如c ++
	 */
	public String getVexNodeType(VexNode vexNode ) {
		SimpleNode treeNode = vexNode.getTreenode();
		String type = "-1_无内容节点";
		if(vexNode.getOutedges().isEmpty()) {
			type = "4_控制流图出口节点";
		}
		else if(vexNode.getInedges().isEmpty()) {
			type = "0_控制流图入口节点";
		}
		else {
			if(treeNode.toString().equals("Declaration")) {
				ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) treeNode.getFirstChildOfType(ASTInitDeclarator.class);
				if(astInitDeclarator.jjtGetNumChildren() == 1) {
					type = "2.2_有定义声明(仅仅声明,未赋值)";
				}
				else if(astInitDeclarator.jjtGetNumChildren() == 2) {
					type = "2.1_有定义声明";
				}
				
			}
			else if(treeNode.toString().equals("ExpressionStatement")) {
				ASTAssignmentExpression assignmentExpression = (ASTAssignmentExpression) treeNode.getFirstChildOfType(ASTAssignmentExpression.class);
				if(assignmentExpression.jjtGetNumChildren() == 1) {
					ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression) assignmentExpression.getFirstChildOfType(ASTPrimaryExpression.class);
					if(astPrimaryExpression.isMethod()) {
						if(list_outsource.contains(astPrimaryExpression.getImage())) {
							type = "5_库函数";
						}
						else {
							type = "1_只有函数f()或者f(c)";
						}
					}
					else {
						type = "6_自增自减运算 比如c ++";
					}
				}
				else if(assignmentExpression.jjtGetNumChildren() == 3) {
					type = "3_无定义声明";
				}
			}
		}
		return type;
	}
	
	
	/**
	 * 判断变量的出现类型
	 * add by lsc 2019/2/15 
	 * 参数3个:变量所在控制流节点vexNode， 变量名varName , 索引 index
	 */
	public String getVarType(VexNode vexNode , String varName , int index) {
		String type = "";
		String string = getVexNodeType(vexNode);
		if(string.contains("0")) {
			type = "参数";
		}
		else if(string.contains("1")) {
			type = "使用点";
		}
		else if(string.contains("2")) {
			SimpleNode simpleNode = vexNode.getTreenode();
			ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) simpleNode.getFirstChildOfType(ASTInitDeclarator.class);
			if(astInitDeclarator.jjtGetNumChildren() == 1) {
				
			}
			else if(astInitDeclarator.jjtGetNumChildren() == 2) {
				
			}
		}
		else if(string.contains("3")) {
			
		}
		else if(string.contains("4")) {
			
		}
		else if(string.contains("5")) {
			
		}
		else if(string.contains("6")) {
			//自增自减情况，当作使用点
			type = "使用点";	
		}
		else if(string.contains("-1")) {
			
		}
		return type;
	}
	
	
	
	/*
	 * add by lsc 2019/1/22 
	 * 分别对目标节点开始的控制流图上的所有可达路径的每条可达路径上的节点进行内容解析，并在控制流图范围内进行溯源
	 * list存储将要分析的变量的名字
	 */
	public void analysis_paths_flowNodes(List<String> path , String funcName , List<String> list) {
		//先分析一条路径
		String pathString = path.get(0);
		String[] strings = pathString.split("<-");
		Map<String, VexNode> map = getMapOfVexNode(funcName);
		
		//初始化
		list.add(args[3]);
        map2.put(funcName, new HashSet<>(Integer.parseInt(args[4])));

		
		for(int i = 0 ; i < strings.length ; i ++) {
			VexNode vexNode = map.get(strings[i]);
			if(getVexNodeType(vexNode).contains("0")) {
				SimpleNode node = vexNode.getTreenode();
				ASTDirectDeclarator astDirectDeclarator = (ASTDirectDeclarator) node.getFirstChildOfType(ASTDirectDeclarator.class);
				
				//没有参数
				if(astDirectDeclarator.isLeaf()) {
					
				}
				//有参数
				else {
					List<SimpleNode> listNodes = astDirectDeclarator.findXpath(".//DirectDeclarator"); 
				}
			}
			//此种情况处理全局变量，暂时可以跳过
			else if(getVexNodeType(vexNode).contains("1")) {
				continue; 
			}
			//有定义声明的情况
			else if(getVexNodeType(vexNode).contains("2")) {
				SimpleNode treeNode = vexNode.getTreenode();
				List<SimpleNode> listNodes = new ArrayList<>();
				listNodes.addAll(treeNode.findXpath(".//DirectDeclarator"));
				listNodes.addAll(treeNode.findXpath(".//PostfixExpression"));
			}
			//无定义声明的情况
			else if(getVexNodeType(vexNode).contains("3")) {
				SimpleNode treeNode = vexNode.getTreenode();
				List<SimpleNode> listNodes = treeNode.findXpath(".//PostfixExpression");
			}
			else if(getVexNodeType(vexNode).contains("4")) {
				continue;
			}
			//碰到外部输入源库函数，可以终止
			else if(getVexNodeType(vexNode).contains("5")) {
				
			}
			// i ++ 等情况
			else if(getVexNodeType(vexNode).contains("6")) {
				SimpleNode treeNode = vexNode.getTreenode();
				List<SimpleNode> listNodes = treeNode.findXpath(".//PostfixExpression");
			}
		}
	}
	
//	/**
//	 * 解析控制流节点的变量内容所在的小语法树节点
//	 */
//	public List analyseVexNode(VexNode vexNode) {
//		if(getVexNodeType(vexNode).contains("0")) {
//			SimpleNode node = vexNode.getTreenode();
//			ASTDirectDeclarator astDirectDeclarator = (ASTDirectDeclarator) node.getFirstChildOfType(ASTDirectDeclarator.class);
//			
//			//没有参数
//			if(astDirectDeclarator.isLeaf()) {
//				
//			}
//			//有参数
//			else {
//				List<SimpleNode> listNodes = astDirectDeclarator.findXpath(".//DirectDeclarator"); 
//			}
//		}
//		//此种情况处理全局变量，暂时可以跳过
//		else if(getVexNodeType(vexNode).contains("1")) {
//			
//		}
//		//有定义声明的情况
//		else if(getVexNodeType(vexNode).contains("2")) {
//			SimpleNode treeNode = vexNode.getTreenode();
//			List<SimpleNode> listNodes = new ArrayList<>();
//			listNodes.addAll(treeNode.findXpath(".//DirectDeclarator"));
//			listNodes.addAll(treeNode.findXpath(".//PostfixExpression"));
//		}
//		//无定义声明的情况
//		else if(getVexNodeType(vexNode).contains("3")) {
//			SimpleNode treeNode = vexNode.getTreenode();
//			List<SimpleNode> listNodes = treeNode.findXpath(".//PostfixExpression");
//		}
//		else if(getVexNodeType(vexNode).contains("4")) {
//		
//		}
//		//碰到外部输入源库函数，可以终止
//		else if(getVexNodeType(vexNode).contains("5")) {
//			
//		}
//		// i ++ 等情况
//		else if(getVexNodeType(vexNode).contains("6")) {
//			SimpleNode treeNode = vexNode.getTreenode();
//			List<SimpleNode> listNodes = treeNode.findXpath(".//PostfixExpression");
//		}
//	}
	
	
	/**
	 * 解析语法树节点，若是表达式(含有等号),获取右边的变量集合
	 */
	public List getRightNodes(SimpleNode node) {
		VexNode vexNode = node.getCurrentVexNode();
		List list = new ArrayList<>();
		SimpleNode assignmentNode = (SimpleNode) node.getFirstChildOfType(ASTAssignmentExpression.class);
		//有定义声明节点(有赋值情况)
		if(getVexNodeType(vexNode).contains("2.1") ) {
			 list = assignmentNode.findChildrenOfType(ASTPostfixExpression.class);
		}
		//有定义声明，但是无赋值情况
		else if(getVexNodeType(vexNode).contains("2.2")) {
			
		}
		//无定义声明节点
		else if(getVexNodeType(vexNode).contains("3")) {
			if (assignmentNode != null && assignmentNode instanceof ASTAssignmentExpression
					&& assignmentNode.jjtGetNumChildren() == 3) {

				ASTAssignmentExpression rightExpr = (ASTAssignmentExpression) assignmentNode.jjtGetChild(2);

				// 取得右侧表达式中所有的变量名列表
			    list = rightExpr.findChildrenOfType(ASTPostfixExpression.class);
			}
		}
		return list;
	}
	

	
	/**
	 * add by lsc
	 * 判断一个变量所在的语法树控制流节点对应的PostfixExpression(也可能是DirectDeclarator)是否在"="左边
	 */
	public boolean isOnleftHandSide(SimpleNode node) {
		VexNode vexNode = node.getCurrentVexNode();
		//有定义声明节点(有赋值情况)
		if(node instanceof ASTDirectDeclarator) {
			return true;
		}

		//无定义声明节点
		else if(getVexNodeType(vexNode).contains("3")) {
			if(node instanceof ASTPostfixExpression) {
				SimpleNode assignmentNode = (SimpleNode) node.getFirstParentOfType(ASTAssignmentExpression.class);
			 	if(assignmentNode instanceof ASTAssignmentExpression && assignmentNode.jjtGetNumChildren()==3){
		       		return true;
		       	}
			}
		}
		
		

		return false;
	}
	
	/**
	 * 根据 函数名， 变量名， 行号， 获取其对应的PostfixExpression(也可能是DirectDeclarator)语法树节点
	 */
	public SimpleNode getSimpleNode(String funcName , String varName , int line) {
		VexNode vexNode = getVexNodeOflocate(funcName, varName, line);
		SimpleNode node = vexNode.getTreenode();
		List list = new ArrayList<>();
		if(! node.findXpath(".//PostfixExpression").isEmpty()) {
			list.addAll(node.findXpath(".//PostfixExpression"));
		}
		if(! node.findXpath(".//DirectDeclarator").isEmpty()) {
			list.addAll(node.findXpath(".//DirectDeclarator"));
		}
		
		for(int i = 0 ; i < list.size() ; i ++) {
			SimpleNode simpleNode = (SimpleNode) list.get(i);
			if(simpleNode instanceof ASTPostfixExpression) {
				if(simpleNode.jjtGetNumChildren() == 1) {
					SimpleNode simpleNode2 = (SimpleNode) simpleNode.jjtGetChild(0);
					if(varName.equals(simpleNode2)) {
						return simpleNode;
					}
				}
				else if(simpleNode.jjtGetNumChildren() > 1) {
					List list2 = simpleNode.findXpath(".//PrimaryExpression");
					boolean flag = true;
					for(int j = 0 ; j < list2.size() ; j ++) {
						SimpleNode node2 = (SimpleNode) list2.get(i);
						if(!varName.contains(node2.getImage())) {
							flag = false;
							break;
						}
					}
					
					if(flag) {
						return simpleNode;
					}
				}
			}
			else if(simpleNode instanceof ASTDirectDeclarator) {
				if(simpleNode.getImage().equals(varName)) {
					return simpleNode;
				}
			}
			
		}
		return node;
		
	}

	/**
     * add by lsc 2019/2/15
     * 判断变量是否在赋值表达式的左边(即定义点)
     * 参数3个，表达式所在控制流结点vexNode , 变量名varName , 变量的索引号index
     */
    public boolean isVarNameAtLeft(VexNode vexNode , String varName , int index)  {
    	String string = getVexNodeType(vexNode);
    	if(index > 1) {
    		return false;
    	}
    	//有定义声明情况
    	if(string.contains("2")) {
			SimpleNode simpleNode = vexNode.getTreenode();
			ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) simpleNode.getFirstChildOfType(ASTInitDeclarator.class);
			//无初始化情况
			if(astInitDeclarator.jjtGetNumChildren() == 1) {
				return false;
			}
			//有初始化情况
			else if(astInitDeclarator.jjtGetNumChildren() == 2) {
				ASTDirectDeclarator astDirectDeclarator = (ASTDirectDeclarator) astInitDeclarator.getFirstChildOfType(ASTDirectDeclarator.class);
				String str = astDirectDeclarator.getImage();
				if(str.equals(varName)) {
					return true;
				}
			}
		}
    	//无定义声明情况 
		else if(string.contains("3")) {
			SimpleNode simpleNode = vexNode.getTreenode();
			ASTPostfixExpression astPostfixExpression = (ASTPostfixExpression) simpleNode.getFirstChildOfType(ASTPostfixExpression.class);
			String varString = getVarNameFromPostNode(astPostfixExpression);
			if(varName.equals(varString)) {
				return true;
			}
		}
		return false;
    }

    
    /**根据post语法树节点获取对应的变量的名字
     * add by lsc 2019/2/17
     */
    public String getVarNameFromPostNode(SimpleNode node) {
    	String varName = "";
    	if(node instanceof ASTPostfixExpression) {
    		if(node.jjtGetNumChildren() == 1) {
    			SimpleNode node2 = (SimpleNode) node.getFirstChildOfType(ASTPrimaryExpression.class);
    			varName = node2.getImage();
    		}
    		else {
    			
    			if(node.getOperators().contains(".") || node.getOperators().contains("->")) {
    				SimpleNode node2 = (SimpleNode) node.getFirstChildOfType(ASTPrimaryExpression.class);
        			varName = node2.getImage();
        			List<SimpleNode> list = node.findDirectChildOfType(ASTFieldId.class);
        			for(SimpleNode nSimpleNode : list) {
        				String str = "." + nSimpleNode.getImage();
        				varName += str;
        			}
    			}
    			else if(node.getOperators().contains("(")){
    				SimpleNode node2 = (SimpleNode) node.getFirstChildOfType(ASTPrimaryExpression.class);
        			varName = node2.getImage();
        			SimpleNode nSimpleNode = (SimpleNode) node.getFirstChildInstanceofType(ASTPostfixExpression.class);
        			if(nSimpleNode != null) {
        				varName = varName + "(" + getVarNameFromPostNode(nSimpleNode);
        			}
        			
    			}
    		}
    	}
    	
    	return varName;  
    	
    }

}
