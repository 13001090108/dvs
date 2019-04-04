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

public class lianxi implements Serializable {
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

	public lianxi(String[] args) {

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

	

	// add by lsc 用于记录所有函数与其被调用函数集合的映射
	public Map<String, List<String>> map_function = new HashMap<>();

	//记录所有自定义函数的名称
	public List<String> list_function = new ArrayList<>();
	// add by lsc 2019/1/2 用于记录函数的名称与其声明路径的映射
	public Map<String, String> map_function_path = new HashMap<>();
	// add by lsc 2019/1/2 用于记录函数的名称与对应抽象语法树节点的映射
	public Map<String, SimpleNode> map_function_simpleNode = new HashMap<>();

	public static void main(String[] args) throws Exception {
		lianxi test = new lianxi(args);

		test.analyze2();
		System.out.println(test.files);

	}
	
	public void analyze2() throws IOException {
		process();
		getMap_function(cgMap);
		getList_function(cgMap);
		getMap_function_path(cgMap);
		getMap_function_simpleNode(cgMap);
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
	public void setArgs(String[] args) {
		this.args = args;
	}

}
