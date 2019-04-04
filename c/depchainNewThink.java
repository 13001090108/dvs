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

public class depchainNewThink implements Serializable {
	/**
	 * ���л�ID
	 */
	private static final long serialVersionUID = 5802149016969017989L;
	private List<AnalysisElement> elements = new ArrayList<AnalysisElement>();;
	private String analysisDir = "";
	private List<String> files = new ArrayList<String>(); // ���ڴ洢�ռ���������.c�ļ�
	private InterCallGraph interCGraph = InterCallGraph.getInstance(); // �õ�������Щ�������ļ���������ϵ
	private String[] args;
	private Pretreatment pre = new Pretreatment();

	public depchainNewThink(String[] args) {

		// add by lsc 2018/9/20
		// �˴�Ϊ����·���µ��ļ���args[0]��ʾ����·���µ�����.c�ļ���args[1]��ʾ����ָ����.c�ļ�
		this.analysisDir = args[0];
		this.setArgs(args);
		init();
	}

	private HashMap<String, ASTTranslationUnit> astmap = new HashMap<String, ASTTranslationUnit>();
	private HashMap<String, Graph> cfgmap = new HashMap<String, Graph>();
	private HashMap<Graph, String> cfgmap2 = new HashMap<Graph, String>();
	private HashMap<String, CGraph> cgMap = new HashMap<String, CGraph>();

	// add by lsc 2018/10/26 ���ڵõ���Դ������������غ���������ȫ���ı�����NameOccurence
	private static Set<NameOccurrence> set2 = new HashSet<>();

	// �ռ�����·���µ�����.CԴ�ļ�
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

	// ����Ԥ����ĳ�ʼ��
	private void init() {
		pre.setPlatform(PlatformType.GCC);

		File srcFileDir = new File(analysisDir);
		collect(srcFileDir);
	}

	public List<List<String>> list_out = new ArrayList<>();
	public List<List<String>> list_out_thisfile = new ArrayList<>();
	public List<String> list_function = new ArrayList<>();
	public List<String> list_operator = new ArrayList<>();
	// add by lsc ���ڼ�¼���к������䱻���ú������ϵ�ӳ��
	public Map<String, List<String>> map_function = new HashMap<>();
	// add by lsc 2018/11/27�� ���ڼ�¼���к���������ú������ϵ�ӳ��
	public Map<String, List<String>> map_function_contains = new HashMap<>();
	// add by lsc 2018/11/27 ���ڼ�¼��Դ���������к������䱻���ú������ϵ�ӳ��
	public Map<String, List<String>> map_function_internal = new HashMap<>();

	// add by lsc 2018/11/27�����ڼ�¼��Դ����������·�����Ӧ��Ҫ�����ĺ������ϵ�ӳ��
	public Map<List<String>, List<List<String>>> Map_path_HighlightFunction = new HashMap<>();

	// add by lsc 2018/11/28,���ڼ�¼��Ӧÿ·����Ҫ�����ĺ�������
	public List<Set<String>> HighlightFunction = new ArrayList<>();

	// add by lsc 2018/11/29�����ڼ�¼�������ص��ⲿ����Դ
	public List<List<String>> list_out_variable = new ArrayList<>();

	// add by lsc 2018/11/29 , ���ڼ�¼��Ӧ�к�����е��ⲿ����Դ��ӳ��
	public Map<VexNode, List<String>> map_line_list_out_variable = new HashMap<>();

	// add by lsc 2019/1/2 ���ڼ�¼������������������·����ӳ��
	public Map<String, String> map_function_path = new HashMap<>();
	// add by lsc 2019/1/2 ���ڼ�¼�������������Ӧ�����﷨���ڵ��ӳ��
	public Map<String, SimpleNode> map_function_simpleNode = new HashMap<>();

	// add by lsc 2019/1/2
	public List<String> list_outsource = new ArrayList<String>();

	public static void main(String[] args) throws Exception {
		depchainNewThink test = new depchainNewThink(args);
		// motified by lsc 2018/11/29�����۲�����Σ��Ƚ��ⲿ����Դ��ȡ
		// add by lsc 2018/11/12��¼�ⲿ����Դ
		System.out.println(test.analyse1());
		// add by lsc 2019/1/2Ϊ�˻�ȡ���׼����Ϣ

		if (args.length == 5) {

			System.out.println(test.analyse2());// ���������

			// �������ص��ⲿ����Դ��ȡ
			System.out
					.println("���vexNode�ڵ���ⲿ����Դ��ӳ��map_line_list_out_variable�� " + test.getmap_line_list_out_variable());

			test.list_out_variable = test.getList_Out_Valiable(test.getmap_line_list_out_variable());
			System.out.println("����������ص��ⲿ����Դ�� " + test.list_out_variable);

			test.analyse3();
			System.out.println("pathSet3: " + test.pathSet3);

			System.out.println("��Դ·�������������Ƕ����ӳ��:");
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

			System.out.println("���map_function_internal: ");
			for (Map.Entry<String, List<String>> entry : test.map_function_internal.entrySet()) {
				System.out.println(entry.getKey() + ":" + entry.getValue());
			}

			// ����HightlightFunction
			for (String string : test.pathSet3) {
				Set<String> set2 = new HashSet<>();
				String[] strings = string.split("<-");
				for (String string2 : strings) {
					// add by lsc 2018/11/28
					// ���ڽ��·���п��ܰ���map2�в����ڵĺ��������(��Ϊ·�����ü��㣬��map2��������룬��
					// ���Ƿ���ֵ����f()ֻ�����ö�������ֵ���������ᷢ��)
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

			System.out.println("���HighlightFunction:");
			for (Set<String> set2 : test.HighlightFunction) {
				for (String string : set2) {
					System.out.print(string + " ");
				}
				System.out.println();
			}

			System.out.println("�������������");
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
	 * add by lsc 2019/1/2 ��ȡ��Ӧ���
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
	 * ������.CԴ�ļ����ν��д���Ԥ���롢����������ȫ�ֺ������ù�ϵͼ
	 * 
	 * @throws IOException
	 */
	private void process() throws IOException {
		// ��һ����������.CԴ�ļ�����Ԥ����
		PreAnalysis();

		// �ڶ���������ȫ�ֺ������ù�ϵͼ
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
			// Ԥ����֮���.IԴ�ļ�
			String afterPreprocessFile = null;
			List<String> include = new ArrayList<String>();

			List<String> macro = new ArrayList<String>();
			afterPreprocessFile = pre.pretreat(srcFile, include, macro);// ���ø���������Ԥ����ָ�������м��ļ�

			try {
				String temp = element.getFileName();
				// ���������﷨��
				System.out.println("���ɳ����﷨��...");
				System.out.println(afterPreprocessFile);
				CParser parser = CParser.getParser(new CCharStream(new FileInputStream(afterPreprocessFile)));
				ASTTranslationUnit root = parser.TranslationUnit();
				astmap.put(srcFile, root);// ���﷨�����ڴ��ͨ���ļ�������

				// �������ű�
				System.out.println("���ɷ��ű�...");
				ScopeAndDeclarationFinder sc = new ScopeAndDeclarationFinder();
				root.jjtAccept(sc, null);
				OccurrenceAndExpressionTypeFinder o = new OccurrenceAndExpressionTypeFinder();
				root.jjtAccept(o, null);

				// ����ȫ�ֺ������ù�ϵ
				System.out.println("����ȫ�ֺ������ù�ϵ...");
				root.jjtAccept(new InterMethodVisitor(), element);

				// �ļ��ں������ù�ϵͼ
				System.out.println("�����ļ��ں������ù�ϵ...");
				CGraph g = new CGraph();
				((AbstractScope) (root.getScope())).resolveCallRelation(g);
				List<CVexNode> list = g.getTopologicalOrderList(element);
				Collections.reverse(list);
				cgMap.put(srcFile, g);

				// ���ɿ�����ͼ
				System.out.println("���ɿ�����ͼ...");
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

				// ���ɶ���ʹ����
				System.out.println("���ɶ���ʹ����...");

				/**
				 * add by lsc 2018/9/14�˴��ȽϹؼ��ĵ�����ASTTranslationUnit.java�е�
				 * public Object jjtAccept(CParserVisitor visitor, Object data)
				 * ���� DUAnalysisVisitor.java�е�visit������
				 * ֮��initDefUse(),��֮��AbstractScope.java�е�
				 * checkOccurrenceType()����"��������"������NameOccurrence��
				 */
				root.jjtAccept(new DUAnalysisVisitor(), null);

				// ����SCVP
				System.out.println("����scvp...");

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
		// �˴����Դ������������ȡ��·����Ϣ,2018/11/30 add by lsc
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

	// ȫ�ֱ���map2�д洢��ÿ�������������Դ����к�
	private Map<String, Set<Integer>> map2 = new HashMap<>();

	// List<List<VexNode>> paths = new ArrayList<>();
	List<String> paths = new ArrayList<>();

	public Map<String, Set<Integer>> analyse2() throws Exception {
		findAstOfVariable findAstOfVariable = new findAstOfVariable();
		findAstOfVariable.main(args);
		list_operator = findAstOfVariable.getList_Operator();

		System.out.println(list_operator.toString());
		prepare();
		process();

		// ��ȡҪ�������NameOccurrence
		// NameOccurrence occ = locate(args[1], args[2], args[3],
		// Integer.valueOf(args[4]));
		//
		// VexNode vexNode = getVexNodeOflocate(args[2], args[3],
		// Integer.valueOf(args[4]));
		// System.out.println(vexNode + " " + vexNode.getTreenode());
		// SimpleNode simpleNode = getSimpleNodeOflocate(args[2], 1, args[3],
		// Integer.valueOf(args[4]));
		// System.out.println(simpleNode);
		//
		// Graph graph11 = cfgmap.get(args[2]);
		// for (Map.Entry<String, NameOccurrence> map :
		// graph11.getOcctable().entrySet()) {
		// String key = map.getKey();
		// NameOccurrence value = map.getValue();
		// System.out.println(key + " " + value);
		// }

		// add by lsc 2019/1/11
		String funcName = args[2];
		String varName = args[3];
		int line = Integer.parseInt(args[4]);
		VexNode vexNode = getVexNodeOflocate(funcName, varName, line);

		// ��ÿ���ڵ��ǰ���ڵ�
		getVexNodeOfPreMap(vexNode);
		// ��for-whileѭ��
		// paths.clear();
		// paths = getPath_test(vexNode,paths);
		//

		set_path_node.clear();
		paths.clear();
		paths = getPath100(vexNode, paths);
		System.err.println("paths : ");
		Set<String> set = new HashSet<>();
		for (String str : paths) {
			set.add(str);
			System.out.println(str);
		}
		System.err.println("set_path_node: " + set_path_node.toString());
		System.err.println("paths��Ԫ�ظ���Ϊ: " + paths.size());
		System.err.println("set��Ԫ�ظ���Ϊ: " + set.size());

		// generate2(occ);
		//
		// System.out.println(vis.toString());
		// System.out.println("�ź���׷�������" + VariableOfSort.toString());
		//
		// System.out.println("map2:");
		return map2;
	}

	// public HashSet<String> pathSet = new HashSet<String>();
	// Ӧ�ѿ���Ҫ�󣬽�����·����ϵ����String���ʹ洢��LinkedList��ʽ�洢
	public HashSet<String> pathSet = new HashSet<>();
	public LinkedList<String> linkedList = new LinkedList<>();

	/**
	 * 
	 * @param occ
	 */
	private void generate2(NameOccurrence occ) {
		DepGraphNode g = new DepGraphNode(occ);

		// ���·������
		pathSet.clear();

		// ����µ�·������
		paths.clear();

		// ���Set����������׼���洢������Ϣ(NameOccurrence),��set����������������
		vis.clear();
		VariableOfSort.clear();

		// ��dfs������ģ��ݹ飬�����ֵ��������Ϊ�����ṩg,��ȫ�ֱ������������������ĵ��ù�ϵ�������map2��¼
		// dfs(occ, g, 0, 1);

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
		// ��ȡҪ�������NameOccurrence
		NameOccurrence occ = locate(args[1], args[2], args[3], Integer.valueOf(args[4]));

		DepGraphNode g = new DepGraphNode(occ);

		// ���Set����������׼���洢������Ϣ(NameOccurrence),��set����������������
		vis.clear();

		// ��dfs������ģ��ݹ飬�����ֵ��������Ϊ�����ṩg,��ȫ�ֱ������������������ĵ��ù�ϵ�������map2��¼
		dfs(occ, g, 0, 1);

		return map_line_list_out_variable;
	}

	/**
	 * ��ӡ�������ڸ����ڵ��scvp����Ϣ
	 * 
	 * @param funcName
	 *            Ϊ�˿����л��÷����ܱ����ã�����private����ȥ�� 2018/10/17 add by lsc
	 */
	void listSCVP(String funcName) {
		Graph cfg = cfgmap.get(funcName);
		JSONObject jsonObject = new JSONObject(true);

		GraphVisitor visitor = new DepChainUtil.listSCVPVisitor();
		cfg.numberOrderVisit(visitor, jsonObject);

		// modify by lsc 2018/9/18��仰Ҫ�ú÷���
		System.out.println(JSON.toJSONString(jsonObject, true));
	}

	private Map<String, Set<String>> vexMap = new HashMap<>();
	private Map<String, Boolean> condMap = new HashMap<>();
	private Map<String, Boolean> condLineMap = new HashMap<>();

	/*
	 * ��ȡ������ĵ���·����ϵ��Ϣ noted by lsc 2018/10/26
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

	// add by lsc 2018/11/28��Ϊ��׷���ź����ķ������
	private List<NameOccurrence> VariableOfSort = new ArrayList<>();

	/*
	 * add by lsc 2019/1/12 ���ݵ�ǰ�������ڵ�õ���ǰ������ͼ�Ͻڵ�������ڵ��mapӳ��
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
	 * add by lsc 2019/1/12 �ж������ڵ��Ƿ�������
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
	 * ���ݸ�����whileѭ����ڻ�ȡ����while�ջ���·����ע������ڵ���while
	 */
	public String getWhilePathSingle(VexNode vexNode) {
		Map<String, VexNode> map = getMapOfVexNode(vexNode);
		String whilepath = "";
		if (vexNode.toString().contains("while_head")) {
			String startforhead = vexNode.toString();
			while (!whilepath.contains("while_head")) {
				VexNode vexNode1;
				if (!whilepath.isEmpty()) {
					int length = whilepath.split("<-").length;
					vexNode1 = map.get(whilepath.split("<-")[length - 1]);
				} else {
					vexNode1 = vexNode;
				}

				Hashtable<String, Edge> hashtable = vexNode1.getInedges();
				Set<String> set = hashtable.keySet();
				for (String string : set) {
					Edge edge = hashtable.get(string);
					VexNode vexNode2 = edge.getTailNode();
					// ��û����while��ʱ�򣬽ڵ��ܳ�������whileѭ���ջ��������ǰ����֧��ʱ����
					if (vexNode2.getSnumber() < vexNode.getSnumber()) {
						continue;
					} else {
						whilepath = whilepath + "<-" + vexNode2.toString();
					}
				}
			}
		}
		return whilepath;
	}

	/*
	 * ���ݸ�����whileѭ����ڽڵ��ȡ����while�ջ���·��,ע�����Զ���whileѭ���ջ�
	 */
	public String getWhilePathMultiple(VexNode vexNode) {
		Map<String, VexNode> map = getMapOfVexNode(vexNode);
		String whilepath = "";
		if (vexNode.toString().contains("while_head")) {
			String startforhead = vexNode.toString();
			while (!whilepath.contains(startforhead)) {
				VexNode vexNode1;
				if (!whilepath.isEmpty()) {
					int length = whilepath.split("<-").length;
					vexNode1 = map.get(whilepath.split("<-")[length - 1]);
				} else {
					vexNode1 = vexNode;
				}

				Hashtable<String, Edge> hashtable = vexNode1.getInedges();
				Set<String> set = hashtable.keySet();
				for (String string : set) {
					Edge edge = hashtable.get(string);
					VexNode vexNode2 = edge.getTailNode();
					// ��û����while��ʱ�򣬽ڵ��ܳ�������forѭ���ջ��������ǰ����֧��ʱ����
					if (vexNode2.getSnumber() < vexNode.getSnumber()) {
						continue;
					} else {
						whilepath = whilepath + "<-" + vexNode2.toString();
						if (vexNode2.toString().contains("while_head")) {
							if (!whilepath.contains(getWhilePathMultiple(vexNode2))) {
								// �˴�ע�⣬Ӧ���滻Ϊ����
								whilepath += getWhilePathMultiple(vexNode2);

								// System.out.println("����ѭ��:"+
								// getForPathSingle(vexNode2));

							}

							Hashtable<String, Edge> table = vexNode2.getInedges();
							Set<String> set_current = table.keySet();
							for (String s_current : set_current) {
								Edge edge2 = table.get(s_current);
								VexNode vexNode_current = edge2.getTailNode();
								if (vexNode_current.getSnumber() < vexNode2.getSnumber()) {
									whilepath += "<-" + vexNode_current.toString();
								}
							}

						}
					}
				}

			}
		}
		return whilepath;
	}

	/*
	 * ���ݸ�����forѭ����ڽڵ��ȡ����for�ջ���·��,ע���ǻ�ȡ��ǰfor�ջ��������ڵ�ǰ(̫����) add by lsc 2019/1/12��
	 */
	public String getForPathSingle(VexNode vexNode) {
		Map<String, VexNode> map = getMapOfVexNode(vexNode);
		String forpath = "";
		if (vexNode.toString().contains("for_head") || vexNode.toString().contains("while_head")) {
			String startforhead = vexNode.toString();
			String str = "";
			if (vexNode.toString().contains("for_head")) {
				str = "for_head";
			}
			if (vexNode.toString().contains("while_head")) {
				str = "while_head";
			}

			while (!forpath.contains(str)) {
				VexNode vexNode1;
				if (!forpath.isEmpty()) {
					int length = forpath.split("<-").length;
					vexNode1 = map.get(forpath.split("<-")[length - 1]);
				} else {
					vexNode1 = vexNode;
				}

				Hashtable<String, Edge> hashtable = vexNode1.getInedges();
				Set<String> set = hashtable.keySet();
				for (String string : set) {
					Edge edge = hashtable.get(string);
					VexNode vexNode2 = edge.getTailNode();
					// ��û����while��ʱ�򣬽ڵ��ܳ�������forѭ���ջ��������ǰ����֧��ʱ����
					if (vexNode2.getSnumber() < vexNode.getSnumber()) {
						continue;
					} else {
						forpath = forpath + "<-" + vexNode2.toString();
					}
				}
			}
		}
		return forpath;
	}

	/*
	 * ���ݸ�����forѭ����ڽڵ��ȡ����for�ջ���·��,ע�����Զ���forѭ���ջ� �����������for�ջ���add by lsc
	 * 2019/1/12/23:21
	 */
	public String getForPathMultiple(VexNode vexNode) {
		Map<String, VexNode> map = getMapOfVexNode(vexNode);
		String forpath = "";
		if (vexNode.toString().contains("for_head") || vexNode.toString().contains("while_head")) {
			String startforhead = vexNode.toString();
			while (!forpath.contains(startforhead)) {
				VexNode vexNode1;
				if (!forpath.isEmpty()) {
					int length = forpath.split("<-").length;
					vexNode1 = map.get(forpath.split("<-")[length - 1]);
				} else {
					vexNode1 = vexNode;
				}

				Hashtable<String, Edge> hashtable = vexNode1.getInedges();
				Set<String> set = hashtable.keySet();
				for (String string : set) {
					Edge edge = hashtable.get(string);
					VexNode vexNode2 = edge.getTailNode();
					// ��û����while��ʱ�򣬽ڵ��ܳ�������forѭ���ջ��������ǰ����֧��ʱ����
					if (vexNode2.getSnumber() < vexNode.getSnumber()) {
						continue;
					} else {
						forpath = forpath + "<-" + vexNode2.toString();
						if (vexNode2.toString().contains("for_head") || vexNode2.toString().contains("while_head")) {
							String string2 = getForPathSingle(vexNode2);
							if (!forpath.contains(getForPathSingle(vexNode2))) {
								// �˴�ע��
								forpath += getForPathSingle(vexNode2);

								// System.out.println("����ѭ��:"+
								// getForPathSingle(vexNode2));

							}

							Hashtable<String, Edge> table = vexNode2.getInedges();
							Set<String> set_current = table.keySet();
							for (String s_current : set_current) {
								Edge edge2 = table.get(s_current);
								VexNode vexNode_current = edge2.getTailNode();
								if (vexNode_current.getSnumber() < vexNode2.getSnumber()) {
									forpath += "<-" + vexNode_current.toString();
								}
							}

						}

					}
				}

			}

			// ���Ӷ�while����Ĵ�����ֹ��ѭ��
			if (startforhead.contains("while_head")) {
				VexNode cNode = map.get(startforhead);
				Hashtable<String, Edge> table = cNode.getInedges();
				Set<String> set_current = table.keySet();
				for (String s_current : set_current) {
					Edge edge2 = table.get(s_current);
					VexNode vexNode_current = edge2.getTailNode();
					if (vexNode_current.getSnumber() < cNode.getSnumber()) {
						forpath += "<-" + vexNode_current.toString();
					}
				}

			}
		}
		return forpath;
	}

	/*
	 * add by lsc 2019/13/11:46 Ŀ�ģ�Ϊ�˲����� ���ܣ����ݸ���������һ��������ͼ�ڵ��ȡ��ǰ�����������нڵ���ǰ���ڵ��ӳ��
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
			System.out.println("�ڵ����ǰ���ڵ��ӳ�䣺" + node + "   :    " + list);
		}
		return map;
	}

	// add by lsc 2019/1/15�����洢�Ѿ������ʹ��Ľڵ�
	Set<VexNode> set_path_node = new HashSet<>();

	/*
	 * add by lsc 2019/1/15 ���������� һ��ǰ���ڵ㣬��ǰ�Ѽ�¼��·��
	 */
	public List<String> getPathNew(VexNode vexNode, List<String> path) {

		// ��¼��ǰ������ͼ�нڵ����ֺͽڵ��ӳ��
		Map<String, VexNode> map = getMapOfVexNode(vexNode);

		if (vexNode.getInedges().isEmpty()) {
			return path;
		} else {
			if (set_path_node.contains(vexNode)) {
				Hashtable<String, Edge> hashtable = vexNode.getInedges();
				Set<String> set = hashtable.keySet();
				Stack<String> stack = new Stack<>();
				for (String s : set) {
					stack.push(s);
				}
				while (!stack.isEmpty()) {
					String string = stack.pop();
					Edge edge = hashtable.get(string);
					VexNode vexNode2 = edge.getTailNode();
					if (!set_path_node.contains(vexNode2)) {
						getPathNew(vexNode2, path);
					}
				}

			} else {

				if (path.isEmpty()) {
					String pString = vexNode.toString();
					path.add(pString);
					set_path_node.add(vexNode);
					Hashtable<String, Edge> hashtable = vexNode.getInedges();
					Set<String> set = hashtable.keySet();
					Stack<String> stack = new Stack<>();
					for (String s : set) {
						stack.push(s);
					}
					while (!stack.isEmpty()) {
						String string = stack.pop();
						Edge edge = hashtable.get(string);
						VexNode vexNode2 = edge.getTailNode();
						if (!set_path_node.contains(vexNode2)) {
							getPathNew(vexNode2, path);
						}
					}
				} else {
					List<String> temp = new ArrayList<>(path);
					for (String str : temp) {
						int length = str.split("<-").length;
						String str_current = str.split("<-")[length - 1];
						VexNode head = map.get(str_current);
						VexNode tail = vexNode;
						if (IsConnect(head, tail)) {
							path.remove(str);
							String strnew = str + "<-" + tail.toString();
							path.add(strnew);
							set_path_node.add(tail);
							getPathNew(tail, path);
						}
					}
				}
			}
		}

		return path;

	}

	/*
	 * add by lsc 2019/1/15 19:20 ������������һ��ǰ�ڵ㣬�ڶ���ǰ·��
	 */
	public List<String> getPathNew1(VexNode vexNode, List<String> path) {

		// ��¼��ǰ������ͼ�нڵ����ֺͽڵ��ӳ��
		Map<String, VexNode> map = getMapOfVexNode(vexNode);

		if (path.isEmpty()) {
			String string = vexNode.toString();
			path.add(string);
			set_path_node.add(vexNode);
			Hashtable<String, Edge> hashtable = vexNode.getInedges();

			Set<String> lEdges = hashtable.keySet();
			for (String str : lEdges) {
				Edge edge = hashtable.get(str);
				VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�
				if (!set_path_node.contains(vexNode3)) {
					getPathNew1(vexNode3, path);
				}
			}

		} else {
			if (set_path_node.contains(vexNode)) {
				Hashtable<String, Edge> hashtable = vexNode.getInedges();

				Set<String> lEdges = hashtable.keySet();
				for (String str : lEdges) {
					Edge edge = hashtable.get(str);
					VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�
					if (!set_path_node.contains(vexNode3)) {
						getPathNew1(vexNode3, path);
					}
				}

			} else {
				List<String> temp = new ArrayList<>(path);
				for (String str : temp) {
					int length = str.split("<-").length;
					String str2 = str.split("<-")[length - 1];

					VexNode head = map.get(str2);
					VexNode tail = vexNode;

					if (IsConnect(head, tail)) {
						String tempstr = str;

						path.remove(tempstr);
						tempstr = tempstr + "<-" + tail.toString();
						path.add(tempstr);
						set_path_node.add(tail);

					}

					Hashtable<String, Edge> hashtable = tail.getInedges();

					Set<String> lEdges = hashtable.keySet();
					for (String st : lEdges) {
						Edge edge = hashtable.get(st);
						VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�
						if (!set_path_node.contains(vexNode3)) {
							getPathNew1(vexNode3, path);
						}
					}

				}
			}

		}

		return path;

	}
	
	/*
	 * 
	 */
	public List<String> getAllPath(VexNode vexNode , List<String>path , VexNode vexNode_now) {
		System.out.println("��������У�path������"+path.size());
		// ��¼��ǰ������ͼ�нڵ����ֺͽڵ��ӳ��
		Map<String, VexNode> map = getMapOfVexNode(vexNode);

		if (path.isEmpty()) {
			String string = vexNode.toString();
			path.add(string);
			set_path_node.add(vexNode);
			Hashtable<String, Edge> hashtable = vexNode.getInedges();
			if (hashtable.isEmpty()) {
				return path;
			} else {
				getAllPath(vexNode, path, vexNode);
			}

		}

		else {	
			
			List<String> temp = new ArrayList<>(path);
			for (String str : temp) {
				int length = str.split("<-").length;
				String str2 = str.split("<-")[length - 1];
			
				
				VexNode head = map.get(str2);
				VexNode tail = vexNode_now;
				if(IsConnect(head, tail)  ) {
					String tempstr = str;
					path.remove(tempstr);
					tempstr = tempstr + "<-" + vexNode_now.toString();
					path.add(tempstr);
					set_path_node.add(vexNode_now);
				}
			}
			
			Hashtable<String, Edge> hashtable = vexNode_now.getInedges();
			
			if(hashtable.isEmpty()) {
				return path;
			}
			else {
				Set<String> set = hashtable.keySet();
				String[] array = set_to_array_sort(set);
				for(int i = array.length - 1 ; i >= 0 ; i --) {
					Edge edge = hashtable.get(array[i]);
					VexNode vexNodeNew = edge.getTailNode();
					if(!set_path_node.contains(vexNodeNew)) {
						getAllPath(vexNode, path, vexNodeNew);
					}
					else {
						if(vexNodeNew.toString().contains("for_head") || vexNodeNew.toString().contains("while_head")) {
							Hashtable<String, Edge> table = vexNodeNew.getInedges();
							Set<String> set_table = table.keySet();
							for(String string : set_table) {
								Edge edge2 = table.get(string);
								VexNode vexNode2 = edge2.getTailNode();
								if(vexNode2.getSnumber() < vexNodeNew.getSnumber()) {
									getAllPath(vexNode, path, vexNode2);
								}
							}
						}
					}
				}
			}

		}
		
		


		return path;
		
	}
	
	
	/*add by lsc 2019/1/16
	 * �������� ��Ŀ��ڵ��������ǰ·��
	 *���ܣ�����Ŀ��ڵ��ȡ�Ӻ�����ڵ�������пɴ�·��
	 */
	public List<String> getPath100(VexNode vexNode , List<String> path) {
		if (path.isEmpty()) {
		findpath("", vexNode);
		}
		return path;
	}
	
	/*
	 * add by lsc 2019/1/16 ��20:32
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
	 * Ŀ��ڵ� ��Ŀ��ڵ�ǰ��·�� ���������������ڼ���Ŀ��ڵ㵽�������ڵ����пɴ�·��
	 */
	public List<String> getPathLast(VexNode vexNode, List<String> path) {

		System.out.println("��������У�path������"+path.size());
		// ��¼��ǰ������ͼ�нڵ����ֺͽڵ��ӳ��
		Map<String, VexNode> map = getMapOfVexNode(vexNode);

		if (path.isEmpty()) {
			String string = vexNode.toString();
			path.add(string);
			set_path_node.add(vexNode);
			Hashtable<String, Edge> hashtable = vexNode.getInedges();
			if (hashtable.isEmpty()) {
				return path;
			} else {
				getPathLast(vexNode, path);
			}

		}

		else {
			List<String> temp = new ArrayList<>(path);
			for (String str : temp) {
				int length = str.split("<-").length;
				String str2 = str.split("<-")[length - 1];

				VexNode vexNode_str = map.get(str2);
				Hashtable<String, Edge> hashtable = vexNode_str.getInedges();

				if (!hashtable.isEmpty()) {

					Set<String> lEdges = hashtable.keySet();
					String[] array = set_to_array_sort(lEdges);

					for (int i = array.length - 1 ; i >= 0 ; i --) {
						Edge edge = hashtable.get(array[i]);
						VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�
						
						if(!str.contains(vexNode3.toString())) {
							String tempstr = str;

							path.remove(tempstr);
							tempstr = tempstr + "<-" + vexNode3.toString();
							if(!path.contains(tempstr)) {
								path.add(tempstr);
							}
							set_path_node.add(vexNode3);
							getPathLast(vexNode, path);
						}
						else {
							if(get_vexnode_count(str, vexNode3) == 1 ) {
								if( vexNode3.toString().contains("for_head") || vexNode3.toString().contains("while_head")) {
									String tempstr = str;

									path.remove(tempstr);
									tempstr = tempstr + "<-" + vexNode3.toString();
									if(!path.contains(tempstr)) {
										path.add(tempstr);
									}
									
							
//									getPathLast(vexNode, path);
								}
		
							}
							
						}



					}

				}

			}

		}
		
		


		return path;

	}
	
	/*
	 * add by lsc 2019/1/16
	 * ��һ��set�����е����ݽ��������������һ�����鼯��
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
	 * ����һ��·���ַ����а����ض��ڵ����ּ���
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
	 * add by lsc 2019/1/13/10:54 ����������
	 * ��ʼ������Ŀ��ڵ�(���ⲿ�˹������Ŀ��ڵ�),path��Ŀ��ڵ㵽��ڵ����пɴ�·�� ��������˰�������forѭ���ջ��Ŀɴ�·���������⡣
	 */
	public List<String> getPath(VexNode vexNode, List<String> path) {

		// ��¼��ǰ������ͼ�нڵ����ֺͽڵ��ӳ��
		Map<String, VexNode> map = getMapOfVexNode(vexNode);

		// System.err.println(vexNode.getGraph());

		// getVexNodeOfPreMap(vexNode);
		// for(VexNode vexNode2 : vexNode.getGraph().getAllnodes()) {
		// if(vexNode2.toString().contains("for_head") ||
		// vexNode2.toString().contains("while_head")) {
		// System.err.println("�ջ���������"+vexNode2+" "
		// +getForPathMultiple(vexNode2));
		// }
		// }
		//

		//
		// for (VexNode node : vexNode.getGraph().getAllnodes()) {
		// if (node.getSnumber() >= 4 && node.getSnumber() <= 16) {
		// Hashtable<String, Edge> hashtable = node.getInedges();
		// if (!hashtable.isEmpty()) {
		//
		// Set<String> lEdges = hashtable.keySet();
		// List<VexNode> list = new ArrayList<>();
		// for (String string : lEdges) {
		// Edge edge = hashtable.get(string);
		// VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�
		// list.add(vexNode3);
		// }
		// System.out.println(node.getTreenode().getBeginLine() + " " +
		// node.getTreenode() + ":"
		// + node.getTreenode().getBeginColumn() + ":" +
		// node.getTreenode().getEndColumn() + " "
		// + node + " : " + list);
		// }
		// }
		// }

		if (path.isEmpty()) {
			String string = vexNode.toString();
			path.add(string);
			Hashtable<String, Edge> hashtable = vexNode.getInedges();
			if (hashtable.isEmpty()) {
				return path;
			} else {
				getPath(vexNode, path);
			}

		} else {
			List<String> temp = new ArrayList<>(path);
			for (String str : temp) {
				int length = str.split("<-").length;
				String str2 = str.split("<-")[length - 1];

				// ���ڼ�¼for�ջ������Ľڵ�·��
				String strfor = "";
				// ����ǰ�ڵ�Ϊforѭ��ͷ��㣬��Ӧ���ȴ���for�ıջ�

				if (str2.contains("for_head") || str2.contains("while_head")) {
					path.remove(str);

					strfor = getForPathMultiple(map.get(str2));

					// ��for�ջ���·�����
					// temp.remove(str);
					str = str + strfor;
					// temp.add(str);
					path.add(str);

				}
				length = str.split("<-").length;
				str2 = str.split("<-")[length - 1];

				VexNode vexNode2 = map.get(str2);
				Hashtable<String, Edge> hashtable = vexNode2.getInedges();

				if (!hashtable.isEmpty()) {

					Set<String> lEdges = hashtable.keySet();
					for (String string : lEdges) {
						Edge edge = hashtable.get(string);
						VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�

						String tempstr = str;

						path.remove(tempstr);
						tempstr = tempstr + "<-" + vexNode3.toString();
						path.add(tempstr);

						getPath(vexNode, path);
					}

				}

			}

		}

		return path;

	}

	/*
	 * Ŀ��ڵ� ��Ŀ��ڵ�ǰ��·�� ���������������ڴ�����for�ջ�2019/1/12/21:30
	 */
	// public List<String> getPath(VexNode vexNode, List<String> path) {
	//
	// // ��¼��ǰ������ͼ�нڵ����ֺͽڵ��ӳ��
	// Map<String, VexNode> map = getMapOfVexNode(vexNode);
	//
	// // System.err.println(vexNode.getGraph());
	// //
	// // for (VexNode node : vexNode.getGraph().getAllnodes()) {
	// // if (node.getSnumber() >= 4 && node.getSnumber() <= 16) {
	// // Hashtable<String, Edge> hashtable = node.getInedges();
	// // if (!hashtable.isEmpty()) {
	// //
	// // Set<String> lEdges = hashtable.keySet();
	// // List<VexNode> list = new ArrayList<>();
	// // for (String string : lEdges) {
	// // Edge edge = hashtable.get(string);
	// // VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�
	// // list.add(vexNode3);
	// // }
	// // System.out.println(node.getTreenode().getBeginLine() + " " +
	// // node.getTreenode() + ":"
	// // + node.getTreenode().getBeginColumn() + ":" +
	// // node.getTreenode().getEndColumn() + " "
	// // + node + " : " + list);
	// // }
	// // }
	// // }
	//
	// if (path.isEmpty()) {
	// String string = vexNode.toString();
	// path.add(string);
	// Hashtable<String, Edge> hashtable = vexNode.getInedges();
	// if (hashtable.isEmpty()) {
	// return path;
	// } else {
	// getPath(vexNode, path);
	// }
	//
	// } else {
	// List<String> temp = new ArrayList<>(path);
	// for (String str : temp) {
	// int length = str.split("<-").length;
	// String str2 = str.split("<-")[length - 1];
	//
	// // ���ڼ�¼for�ջ������Ľڵ�·��
	// String strfor = "";
	// // ����ǰ�ڵ�Ϊforѭ��ͷ��㣬��Ӧ���ȴ���for�ıջ�
	//
	// // Ϊ�˽�����رջ����⣬��Ҫ��ȷ��¼��ǰ�ڵ�������Ϣ
	// String str2_current = str2;
	//
	// if (str2.contains("for_head")) {
	// path.remove(str);
	//
	// while (!strfor.contains(str2_current)) {
	// VexNode vexNode2 = map.get(str2);
	// Hashtable<String, Edge> tables = vexNode2.getInedges();
	// if (!tables.isEmpty()) {
	// Set<String> set = tables.keySet();
	// for (String string : set) {
	// Edge edge = tables.get(string);
	// VexNode vexNode3 = edge.getTailNode();
	// if (vexNode3.toString().contains("for_init")) {
	// continue;
	// } else {
	// strfor = strfor + "<-" + vexNode3.toString();
	// str2 = vexNode3.toString();
	// }
	// }
	// }
	// }
	//
	// // ��for�ջ���·�����
	// temp.remove(str);
	// str = str + strfor;
	// temp.add(str);
	// path.add(str);
	//
	// }
	//
	// VexNode vexNode2 = map.get(str2);
	// Hashtable<String, Edge> hashtable = vexNode2.getInedges();
	//
	// if (!hashtable.isEmpty()) {
	//
	// Set<String> lEdges = hashtable.keySet();
	// for (String string : lEdges) {
	// Edge edge = hashtable.get(string);
	// VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�
	//
	// // ��Ϊ���洦����for�ջ�������������forǰ�����ڴ���
	// if (vexNode3.toString().contains("for") && str.contains("for_inc")
	// && (!vexNode3.toString().contains("for_init"))) {
	// continue;
	// }
	//
	// String tempstr = str;
	//
	// path.remove(tempstr);
	// tempstr = tempstr + "<-" + vexNode3.toString();
	// path.add(tempstr);
	//
	// getPath(vexNode, path);
	// }
	//
	// }
	//
	// }
	//
	// }
	//
	// return path;
	//
	// }

	// /*
	// * Ŀ��ڵ� ��Ŀ��ڵ�ǰ��·��
	// */
	// public List<List<VexNode>> getPath(VexNode vexNode, List<List<VexNode>>
	// path) {
	//
	//
	// if (path.isEmpty()) {
	// List<VexNode> list = new ArrayList<>();
	// list.add(vexNode);
	// path.add(list);
	// Hashtable<String, Edge> hashtable = vexNode.getInedges();
	// if (hashtable.isEmpty()) {
	// return path;
	// } else {
	// getPath(vexNode, path);
	// }
	//
	// }
	// else {
	// List<List<VexNode>> temp = new ArrayList<>(path);
	// for (List<VexNode> list : temp) {
	// VexNode vexNode2 = list.get(list.size() - 1);
	// Hashtable<String, Edge> hashtable = vexNode2.getInedges();
	//
	// if (!hashtable.isEmpty()) {
	// List<VexNode> lNodes = new ArrayList<>(list);
	//
	// Set<String> lEdges = hashtable.keySet();
	// for (String string : lEdges) {
	// Edge edge = hashtable.get(string);
	// VexNode vexNode3 = edge.getTailNode(); // �����ǰ���ڵ�
	//
	// List<VexNode> lVexNodes = new ArrayList<>(lNodes);
	//
	// lVexNodes.add(vexNode3);
	// path.remove(lNodes);
	// path.add(lVexNodes);
	// getPath(vexNode3, path);
	// }
	//
	// }
	//
	// }
	//
	//
	// }
	//
	//
	//
	// return path;
	//
	// }

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

		// if (vis.contains(occ)) {
		// return;
		// }
		// vis.add(occ);
		// VariableOfSort.add(occ);
		// // count++;
		// if (g == null)
		// return;
		//
		//
		//// System.err.println(occ.getLocation().getCurrentVexNode().getGraph());
		//
		// if(isOnLeftHandSideForArray(occ)) {
		// System.err.println("is left");
		// System.out.println(occ+ " "+ occ.getLocation());
		// List listOfRight = getRightVar(occ.getLocation());
		// for(Object object : listOfRight) {
		// ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression)
		// object;
		//
		// ASTFunctionDefinition astFunctionDefinition = (ASTFunctionDefinition)
		// astPrimaryExpression.getFirstParentOfType(ASTFunctionDefinition.class);
		// System.err.println(map_function_path.get(astFunctionDefinition.getImage()));
		// System.err.println(astFunctionDefinition.getImage());
		// System.err.println(astPrimaryExpression.getImage());
		// System.err.println(astPrimaryExpression.getBeginLine());
		// }
		//
		// VexNode vexNode = occ.getLocation().getCurrentVexNode();
		// System.err.println(occ.getLocation().jjtGetParent().jjtGetParent().jjtGetNumChildren());
		//
		//
		// }else if(! isOnLeftHandSideForArray(occ)) {
		// System.err.println("is right");
		// System.out.println(occ+ " "+ occ.getLocation());
		// }
	}

	/**
	 * add by lsc 2018/12/7��Ϊ���ж���������Ƿ�λ�ڵȺ����
	 * 
	 * @return �жϵ�ǰ�������֣�NameOccurence)�Ƿ�λ�ڣ���࣬���Ƿ�Ϊ������ֵDEF
	 */
	public boolean isOnLeftHandSideForArray(NameOccurrence occ) {
		SimpleNode declarator = null;

		if (occ.getLocation() instanceof ASTPostfixExpression) {
			Node assignment = occ.getLocation().jjtGetParent().jjtGetParent();
			if (assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren() == 3) {
				return true;
			}
		}
		if (occ.getLocation().jjtGetParent() instanceof ASTPostfixExpression) {
			declarator = (ASTPostfixExpression) occ.getLocation().jjtGetParent();
			Node assignment = declarator.jjtGetParent().jjtGetParent();
			if (assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren() == 3) {
				return true;
			}
			// add else branch by cmershen,2016.5.31 ��Ӷ�*p=2���͵�֧��
			else {
				Node child = assignment;
				assignment = assignment.jjtGetParent();
				if (assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren() == 3
						&& child == assignment.jjtGetChild(0)) {
					return true;
				}
			}
		}
		return false;
	}

	/*
	 * add by lsc 2018/12/4 , ȡ�õȺ��ұߵı������б�
	 */
	public List getRightVar(SimpleNode node) {
		Node assignmentNode = node.getFirstParentOfType(ASTAssignmentExpression.class);
		if (assignmentNode != null && assignmentNode instanceof ASTAssignmentExpression
				&& assignmentNode.jjtGetNumChildren() == 3) {

			ASTAssignmentExpression rightExpr = (ASTAssignmentExpression) assignmentNode.jjtGetChild(2);

			// ȡ���Ҳ���ʽ�����еı������б�
			List rightVars = rightExpr.findChildrenOfType(ASTPrimaryExpression.class);
			return rightVars;

		}

		// add by lsc 2018/12/11����ֱ�Ӷ����ʱ������int m = a + 1;
		if (node instanceof ASTDirectDeclarator) {
			ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) node
					.getFirstParentOfType(ASTInitDeclarator.class);
			ASTInitializer astInitializer = (ASTInitializer) astInitDeclarator
					.getFirstChildOfType(ASTInitializer.class);
			List rightVars = astInitializer.findChildrenOfType(ASTPrimaryExpression.class);
			return rightVars;
		}

		return null;
	}

	/*
	 * add by lsc 2018/12/6�����˶�switch�ļ�ӿ��ƴ��� add by lsc 2018/12/6
	 * �жϱ���׷���Ƿ��׷�ݵ�switch�� ����׷�ݽ��򷵻�switch�ڵ�(VexNode),���򷵻�null
	 */
	public VexNode getSwitchVexNode(NameOccurrence occ) {

		List<NameOccurrence> def_temp = occ.getUse_def();
		for (NameOccurrence cNameOccurrence : def_temp) {

			Graph graph1 = cNameOccurrence.getLocation().getCurrentVexNode().getGraph();

			for (VexNode vexNode2 : graph1.getAllnodes()) {
				if (vexNode2.toString().contains("switch_head")) {
					return vexNode2;

				}
			}
		}
		return null;
	}

	/*
	 * add by lsc 2018/12/28 �ж�һ�������Ƿ���switch�����ڲ�
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
	 * add by lsc 2018/11/26 �ж϶�����Ƿ�Ϊ��������
	 */
	public boolean isDefOfConstant(NameOccurrence occ) {

		ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) occ.getLocation()
				.getFirstParentOfType(ASTInitDeclarator.class);
		// motified by lsc 2018/12/6 int b = a���� int b = 1�����������int
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

				// ȡ���Ҳ���ʽ�����еı������б�
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
	 * add by lsc 2018/11/24 �鿴�ñ��������Ƿ�Ϊ += �� -= �� *= ,/=,%=�ȸ���
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
	 * add by lsc 2018/9/19 ��ȡҪ�������NameOccurrence
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
	 * �Ӻ�������ڵ��ȡ�������ڵ㣬���Դ�ASTPostfixExpression.getImage()��ȡ���ú����ĺ����� add by lsc
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
		//
		for (Map.Entry<VexNode, List<String>> entry : map_line_list_out_variable.entrySet()) {
			list_out_variable.add(entry.getValue());
		}
		return list_out_variable;
	}

	public HashSet<String> analyse3() throws Exception {

		getpathSet3(args[2], args[2]);

		System.out.println("������������õ����·������Դ�����");

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

	// add by lsc 2018/12/24
	public HashMap<String, Graph> getCfgmap() {
		return cfgmap;
	}

	/*
	 * add by lsc 2019/1/10 �ɺ����������������кŻ�ȡ��λ��Ŀ�����ͼ�ڵ�
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
	 * add by lsc 2019/1/10 �ɺ��������������������������������ڼ���������)���кŻ�ȡ��λ��ĳ����﷨�����
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

}
