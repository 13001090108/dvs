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
import org.omg.CORBA.ORBPackage.InconsistentTypeCode;

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

public class DepchainNew implements Serializable {
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

	public DepchainNew(String[] args) {

		// add by lsc 2018/9/20
		// �˴�Ϊ����·���µ��ļ���args[0]��ʾ����·���µ�����.c�ļ���args[1]��ʾ����ָ����.c�ļ�
		this.analysisDir = args[1];
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

	public static void main(String[] args) throws Exception {
		DepchainNew test = new DepchainNew(args);

		// motified by lsc 2018/11/29�����۲�����Σ��Ƚ��ⲿ����Դ��ȡ
		// add by lsc 2018/11/12��¼�ⲿ����Դ
		System.out.println(test.analyse1());

		if (args.length == 5) {
			System.out.println(test.analyse2());// ���������

			// �������ص��ⲿ����Դ��ȡ
			test.list_out_variable = test.getList_Out_Valiable(test.getmap_line_list_out_variable());

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
			include.add("C:/Program Files (x86)/DTS/DTS/DTSGCC/include");
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
		args1[0] = args[1];
		tg.main(args1);
		list_out = tg.getList();
		return list_out;
	}

	// ȫ�ֱ���map2�д洢��ÿ�������������Դ����к�
	private Map<String, Set<Integer>> map2 = new HashMap<>();

	public Map<String, Set<Integer>> analyse2() throws Exception {
		findAstOfVariable findAstOfVariable = new findAstOfVariable();
		findAstOfVariable.main(args);
		list_operator = findAstOfVariable.getList_Operator();

		System.out.println(list_operator.toString());

		process();
		// ��ȡҪ�������NameOccurrence
		NameOccurrence occ = locate(args[1], args[2], args[3], Integer.valueOf(args[4]));

		// VexNode vexNode = occ.getLocation().getCurrentVexNode();
		
		generate2(occ);

		System.out.println(vis.toString());
		System.out.println("�ź���׷�������" + VariableOfSort.toString());

		System.out.println("map2:");
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

		// ���Set����������׼���洢������Ϣ(NameOccurrence),��set����������������
		vis.clear();
		VariableOfSort.clear();

		// ��dfs������ģ��ݹ飬�����ֵ��������Ϊ�����ṩg,��ȫ�ֱ������������������ĵ��ù�ϵ�������map2��¼
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
	private void dfs(NameOccurrence occ , DepGraphNode g ,int cond , int depth) {
		if(vis.contains(occ)) {
			return;
		}
		vis.add(occ);
		VariableOfSort.add(occ);
		if(g == null) {
			return;
		}
		
		
	}
	

//	private void dfs(NameOccurrence occ, DepGraphNode g, int cond, int depth) {
//		if (vis.contains(occ)) {
//			return;
//		}
//		vis.add(occ);
//		VariableOfSort.add(occ);
//		// count++;
//		if (g == null)
//			return;
//		// if (depth > 5) return;
//		
//		
//		// add by lsc 2018/10/24 ��ȡ������ (�������ַ�ʽ���ɻ�ȡ������)
//		String func = ((ASTFunctionDefinition) occ.getLocation().getFirstParentOfType(ASTFunctionDefinition.class))
//				.getImage();
//		int line = Integer.valueOf(occ.toString().split(":")[1]);
//
//		if (!map2.containsKey(func)) {
//			map2.put(func, new HashSet<Integer>());
//		}
//		map2.get(func).add(line);
//		
//		
//		
//		//add by lsc 2018/12/18
//		VexNode vexNode1 = occ.getLocation().getCurrentVexNode();
//		Graph graph1 = vexNode1.getGraph();
//		SimpleNode simpleNode = vexNode1.getTreenode(); 
//		System.out.println(simpleNode+":"+occ.getLocation());
//		for(VexNode vexNode2 : graph1.getAllnodes()) {
//			System.err.println(vexNode2+": " +vexNode2.getOccurrences() + vexNode2.getTreenode());
//			System.err.println(vexNode2+" ��ǰ���ڵ��б�:" +getPreVexNode(vexNode2));
//		}
//		
//
//		
//	
//	
//		
//		if (occ.getOccurrenceType() == OccurrenceType.DEF) {
//
//			
//				SCVPString scvp = occ.getSCVP();
//				List<String> vlist = scvp.getOccs();
//			
//				// add test by lsc 2018/10/9
//				System.out.println("test2018/10:" + vlist.toString());
//
//				for (String v : vlist) {
//					Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
//					NameOccurrence o = cfg.getOcctable().get(v);
//					if (o.getImage().toString().equals(occ.getImage()))
//						continue;
//					DepGraphNode g2 = g.addChild(o);
//				
//					dfs(o, g2, cond, depth + 1);
//				}
//				String s = scvp.getStructure();
//
//				System.out.println("s" + s + "==============================================================");
//				if (s.contains("Function:")) { // ����ֵ
//					int id = s.indexOf("Function");
//					s = s.substring(id);
//					String[] fs = s.trim().split("Function:");
//
//					for (String string : fs)
//						System.out.println("�������ƣ�" + string
//								+ "==============================================================");
//
//					ASTStatement statement = (ASTStatement) occ.getLocation()
//							.getFirstParentOfType(ASTStatement.class);
//
//					System.out.println("statement:" + statement
//							+ "==============================================================");
//
//					List<Node> priList = statement.findChildrenOfType(ASTPrimaryExpression.class);
//					System.out.println(
//							"priList" + priList + "==============================================================");
//					for (String f : fs) {
//						for (Node n : priList) {
//							ASTPrimaryExpression pri = (ASTPrimaryExpression) n;
//							if (pri.isMethod() && pri.getImage().equals(f)) {
//								// 2011.6.24
//								// Ŀǰ��δ��������⣺����Ǻ���ָ����ʽ�ĺ������ã���λ�ȡ��ȷ�ĺ������ã�
//
//								System.out.println(pri.getMethodDecl()
//										+ "==============================================================");
//								if (pri.getMethodDecl() == null)
//									continue;
//								Method m = pri.getMethodDecl().getMethod();
//								System.out.println("Method:" + m
//										+ "==============================================================");
//								SimpleNode entNode = pri.getMethodDecl().getMethodNameDeclaratorNode();
//								System.out.println("entNode: " + entNode
//										+ "==============================================================");
//								Graph cfg = null;
//								if (entNode instanceof ASTFunctionDefinition)
//									cfg = ((ASTFunctionDefinition) entNode).getGraph();
//								List<SCVPString> ret = m.getReturnList();
//								System.out.println("m.getReturnList:" + ret.toString()
//										+ "==============================================================");
//								for (SCVPString scvpString : ret) {
//									for (String v : scvpString.getOccs()) {
//										if (cfg != null) {
//											NameOccurrence o = cfg.occtable.get(v);
//											DepGraphNode g2 = g.addChild(o);
//											dfs(o, g2, cond, depth + 1);
//										}
//									}
//								}
//							}
//						}
//					}
//				}
//			}
//
//		
//		  if (occ.getOccurrenceType() == OccurrenceType.ENTRANCE) {
//				// ��÷����������﷨���ڵ�,(֮����Լ�ӻ�ȡ�������������Ϣ)
//				ASTFunctionDefinition funcdef = (ASTFunctionDefinition) occ.getLocation()
//						.getFirstParentOfType(ASTFunctionDefinition.class);
//
//				// add test by lsc 2018/11/26
//				// ����˲�����������ȷ�����⣬ԭ������������ȡ��ʽ��������(���ܱ�֤funcdef.getScope()�Ĳ��������µĴ������������﷨������֤��ȷ).
//				String[] ParameterList = new String[funcdef.getParameterCount()];
//				int count = 0;
//				System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
//				System.out.println(funcdef.getImage());
//				List<SimpleNode> list = funcdef.findXpath(".//ParameterDeclaration");
//				for (SimpleNode simpleNode1 : list) {
//					List<SimpleNode> list2 = simpleNode1.findXpath(".//Declarator");
//					for (SimpleNode simpleNode22 : list2) {
//						System.out.println(simpleNode22.getImage() + ":" + simpleNode22.getBeginColumn());
//						ParameterList[count++] = simpleNode22.getImage();
//					}
//				}
//
//				System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
//
//				int index = 0;
//				// boolean isFind = false; //�ж��Ƿ��ҵ�
//
//				System.out.println("��ǰ����" + occ.toString().split(":")[0]);
//
//				for (int i = 0; i < count; i++) {
//					if (occ.toString().split(":")[0].equals(ParameterList[i])) {
//						index = i + 1;
//						break;
//					}
//				}
//
//				System.out.println("�ó��˱�����" + occ.toString().split(":")[0] + "��indexΪ:" + index);
//
//				if (funcdef != null) {
//					// ��һ��HashMap����¼ǰ��ժҪ�����������ú����������⣬������������Դ����
//					// �Ҿ�����Ҫ���һ������������index���������ֵ�����Դ�ĸ����� 2018/9/27 lsc
//					HashMap<Position, ArrayList<SCVPString>> callerInfo = funcdef.getDecl().getMethod().getCallerInfo();
//					for (Position p : callerInfo.keySet()) {
//						// add by lsc 2018/9/27
//
//						// System.out.println("test:" + index);
//
//						// System.out.println("test��" + p.toString());
//						// System.out.println("scvpstring :" +
//						// callerInfo.get(p).toString());
//
//						Graph cfg = cfgmap.get(p.getFunctionName());
//						if (cfg != null) {
//							for (SCVPString scvp : callerInfo.get(p)) {
//
//								String fileName = p.getFileName();
//								String funcName = p.getFunctionName();
//								String symbolName = scvp.getVar();
//
//								// add test by lsc
//								// System.out.println("test:" + symbolName);
//								// System.out.println("index:" + p.getIndex());
//								int line1 = p.getBeginLine();
//
//								// ���ڶԱȲ����������о�ȷ��Դ add by lsc 2018/10/9
//								if (p.getIndex() == index) {
//									System.out.println("�к�:" + line1 + "  ������ " + symbolName + "  ������" + index);
//									NameOccurrence occ2 = locate(fileName, funcName, symbolName, line1);
//									System.out.println("occ2���ݣ�" + occ.toString());
//
//									if (occ2 == null)
//										continue;
//									DepGraphNode g3 = g.addChild(occ2);
//									dfs(occ2, g3, cond, depth + 1);
//
//									for (String v : scvp.getOccs()) {
//
//										System.out.println(scvp.getOccs() + "lsc");
//
//										NameOccurrence o = cfg.occtable.get(v);
//										DepGraphNode g2 = g.addChild(o);
//										dfs(o, g2, cond, depth + 1);
//									}
//
//								}
//
//							}
//						}
//					}
//				}
//			}
//		  
//		  else {
//				SimpleNode simpleNode2 = occ.getLocation();
//				
//				if(isOnLeftHandSideForArray(occ)) {
//					//���Ƕ�����������Ⱥ����
//				    //���Ƕ��� int a = b ;
//					if(simpleNode2 instanceof ASTDirectDeclarator ) {
//						List list = getRightVar(simpleNode2);
//						for(Object object : list) {
//							if(object instanceof ASTPrimaryExpression) {
//								for(NameOccurrence nameOccurrence :occ.getLocation().getCurrentVexNode().getOccurrences()) {
//									if(!nameOccurrence.equals(occ)) {
//										DepGraphNode g2 = g.addChild(nameOccurrence);
//										dfs(nameOccurrence, g2, cond, depth + 1);
//									}
//								}
//							}
//						}
//						System.err.println("list: "+list.toString()+"  "+occ);
//					}
//					
//					//c = a + b��ʽ
//					else if(simpleNode2 instanceof ASTPrimaryExpression) {
//						List list = getRightVar(simpleNode2);
//						if(list != null) {
//							for(Object object : list) {
//								if(object instanceof ASTPrimaryExpression) {
//									for(NameOccurrence nameOccurrence :occ.getLocation().getCurrentVexNode().getOccurrences()) {
//										if(!nameOccurrence.equals(occ)) {
//											DepGraphNode g2 = g.addChild(nameOccurrence);
//											dfs(nameOccurrence, g2, cond, depth + 1);
//										}
//									}
//								}
//							}
//							System.err.println("list: "+list.toString()+"  "+occ);
//						}
//						
//					}
//					
//				}
//					
//					//����ʹ�õ���������Ⱥ��ұ�
//					else  {
//						
//						//Ѱ��ǰ���ڵ�취
//						boolean flag = false;
//						VexNode vexNode2 = occ.getLocation().getCurrentVexNode();
//						List<VexNode> list = getPreVexNode(vexNode2);
//						while(!flag) {
//							
//							for(VexNode vexNode : list) {
//								for(NameOccurrence nameOccurrence : vexNode.getOccurrences()) {
//									if(nameOccurrence.getImage().equals(occ.getImage()) && isOnLeftHandSideForArray(nameOccurrence)) {
//										flag = true;
//										DepGraphNode g2 = g.addChild(nameOccurrence);
//										dfs(nameOccurrence, g2, cond, depth + 1);
//									}
//								}
//							}
//							
//							if(list == null || list.size() == 0) break;
//							int num = list.size();
//							if(flag == false) {
//								for(int i = 0 ; i < num ; i ++) {
//									VexNode vexNode = list.get(i);
//									for(VexNode vexNode3 : getPreVexNode(vexNode)) {
//										if(!list.contains(vexNode3)) {
//											list.add(vexNode3);
//										}
//									}
//								}
//								
//								for(int i = 0 ; i < num ; i ++) {
//									list.remove(list.get(0));
//								}
//							}
//							
//						}
//						
//						
//						//������ͼֱ�ӱ����ⷨ
////						boolean flag = false;
////						VexNode vexNode2 = occ.getLocation().getCurrentVexNode();
////						VexNode need = null;
////						
////						Graph graph = vexNode2.getGraph();
////						for(VexNode vexNode : graph.getAllnodes()) {
////							if(vexNode.getSnumber() < vexNode2.getSnumber()) {
////								for(NameOccurrence nameOccurrence : vexNode.getOccurrences()) {
////									if(nameOccurrence.getImage().equals(occ.getImage()) && isOnLeftHandSideForArray(nameOccurrence)) {
////										need = vexNode;
////									}
////								}
////							}
////						}
////						
////						if(need != null) {
////							for(NameOccurrence nameOccurrence : need.getOccurrences()) {
////								if(nameOccurrence.getImage().equals(occ.getImage()) && isOnLeftHandSideForArray(nameOccurrence)) {
////									flag = true;
////									DepGraphNode g2 = g.addChild(nameOccurrence);
////									dfs(nameOccurrence, g2, cond, depth + 1);
////								}
////							}
////						}
//						
//						
//						
//					}
//				
//				
//		  }
//		
//	
//			
//	}
//		
	
	/*
	 * ��ȡǰ���ڵ��б�add by lsc 2018/12/19
	 */
	public List<VexNode> getPreVexNode(VexNode vexNode) {
		if(vexNode == null) return null;
		List<VexNode> ansVexNode = new ArrayList<>();
		Graph graph = vexNode.getGraph();
		for(VexNode vexNode2 : graph.getAllnodes()) {
			for(Edge edge : vexNode2.getOutedges().values()) {
				if(edge.getHeadNode() == vexNode) {
					ansVexNode.add(vexNode2);
				}
			}
		}
		return ansVexNode;
	}

		
		

//		try {
//
//			// add by lsc 2018/10/24 ��ȡ������ (�������ַ�ʽ���ɻ�ȡ������)
//			String func = ((ASTFunctionDefinition) occ.getLocation().getFirstParentOfType(ASTFunctionDefinition.class))
//					.getImage();
//			int line = Integer.valueOf(occ.toString().split(":")[1]);
//
//			if (!map2.containsKey(func)) {
//				map2.put(func, new HashSet<Integer>());
//			}
//			map2.get(func).add(line);
//
//			// add by lsc 2018/11/29Ϊ����ӱ������ⲿ����Դ�ڵ���Ϣ
//			VexNode vexNode = occ.getLocation().getCurrentVexNode();
//			// System.out.println("vexNode: lsc " + vexNode);
//
//			List<NameOccurrence> list1 = vexNode.getOccurrences();
//
//			for (List<String> list : list_out) {
//				if (list.contains(args[1])) {
//					list_out_thisfile.add(list);
//				}
//			}
//
//			for (List<String> list : list_out_thisfile) {
//				if (list.get(2) != null && list.get(2).equals(String.valueOf(line))) {
//					if (!map_line_list_out_variable.containsKey(vexNode)) {
//
//						map_line_list_out_variable.put(vexNode, list);
//					}
//				}
//			}
//
//			// add by lsc 2018/9/16
//			if (cond == 1) {
//
//				condLineMap.put(func + "_" + occ.toString().split(":")[1], true);
//				// System.out.println(func +"_"+
//				// occ.toString().split(":")[1]+"lsc");
//				// g.setCond(true);
//			} else {
//
//			}
//			if (occ == null)
//				return;
//
//			if (occ.getOccurrenceType() == OccurrenceType.USE) {
//
//				// add by lsc 2018/12/4 �����˶�����Ĵ���
//
//				if (occ.getLocation().getOperators().equals("[")) {
//					Graph graph = occ.getLocation().getCurrentVexNode().getGraph();
//					System.err.println(graph);
//					System.out.println(occ);
//
//					// add by lsc 2018/12/7�� ��������[]�в��Ǳ������ǳ���������num[1]
//					if (occ.toString().contains("[")) {
//						VexNode cVexNode = null; // ���ڼ�¼occǰ���������occ�����������ͬ�������ڽڵ�
//						for (VexNode vexNode2 : graph.getAllnodes()) {
//							for (NameOccurrence cNameOccurrence : vexNode2.getOccurrences()) {
//								if (cNameOccurrence.toString().split(":")[0].equals(occ.toString().split(":")[0])
//										&& vexNode2.getSnumber() < occ.getLocation().getCurrentVexNode().getSnumber()
//										&& isOnLeftHandSideForArray(cNameOccurrence)) {
//									cVexNode = vexNode2;
//								}
//							}
//						}
//
//						// ��ǰ��������num[1]��ֵ�Ķ������
//						if (cVexNode != null) {
//							for (NameOccurrence cNameOccurrence : cVexNode.getOccurrences()) {
//
//								DepGraphNode g2 = g.addChild(cNameOccurrence);
//								dfs(cNameOccurrence, g2, cond, depth + 1);
//
//							}
//						}
//						// ��ǰ��û��num[1]��ֵ�Ķ���������Ǿ���num����Ķ����
//						else {
//							NameOccurrence nameOccurrence = occ;
//							boolean flag = false;
//							for (VexNode vexNode2 : graph.getAllnodes()) {
//								for (NameOccurrence nameOccurrence1 : vexNode2.getOccurrences()) {
//									if (nameOccurrence1.getLocation().getOperators().equals("[")) {
//										nameOccurrence = nameOccurrence1;
//										System.out.println(nameOccurrence + "lsc" + vexNode2);
//										flag = true;
//										break;
//									}
//								}
//								if (flag) {
//									break;
//								}
//							}
//						}
//					} else {
//						NameOccurrence nameOccurrence = occ;
//						boolean flag = false;
//						for (VexNode vexNode2 : graph.getAllnodes()) {
//							for (NameOccurrence nameOccurrence1 : vexNode2.getOccurrences()) {
//								if (nameOccurrence1.getLocation().getOperators().equals("[")) {
//									nameOccurrence = nameOccurrence1;
//									System.out.println(nameOccurrence + "lsc" + vexNode2);
//									flag = true;
//									break;
//								}
//							}
//							if (flag) {
//								break;
//							}
//						}
//						DepGraphNode g2 = g.addChild(nameOccurrence);
//						dfs(nameOccurrence, g2, cond, depth + 1);
//					}
//				}
//
//				// add by lsc 2018/12/6�����˶�switch�ļ�ӿ��ƴ���
//
//				// add by lsc 2018/12/7�����������ʧ��switch����Լ�������ļ���׷��
//				if (occ.getLocation().getCurrentVexNode().toString().contains("switch")) {
//					List<NameOccurrence> def = occ.getUse_def();
//					for (NameOccurrence o : def) {
//						DepGraphNode g2 = g.addChild(o);
//						dfs(o, g2, cond, depth);
//					}
//				}
//
//				if (!occ.getLocation().getCurrentVexNode().toString().contains("switch")) {
//					VexNode vexNode3 = getSwitchVexNode(occ);
//					if (vexNode3 != null) {
//						List<NameOccurrence> nameOccurrences = vexNode3.getOccurrences();
//						System.out.println(nameOccurrences + "switch");
//
//						// ��switch����Լ�����ǽ��������������Դ����
//						for (NameOccurrence cNameOccurrence : nameOccurrences) {
//							DepGraphNode g2 = g.addChild(cNameOccurrence);
//							dfs(cNameOccurrence, g2, cond, depth + 1);
//						}
//
//						// add by lsc 2018/12/7
//						// ���ǽ�switch������·����������(����Ҫ����ڵ������image ==
//						// occ.image)������Ӧ�ø�����һЩ�����Ը���ʦ̽�֡�
//						Graph graph = vexNode3.getGraph();
//						System.out.println(graph + "lsc" + occ);
//
//						// ���ڼ�¼switch case�Ŀ�ʼ�ڵ����ֹ�ڵ�
//						int start = 0, end = 0;
//
//						for (VexNode cVexNode : graph.getAllnodes()) {
//
//							if (cVexNode.toString().contains("switch_head")) {
//								start = cVexNode.getSnumber();
//							}
//							if (cVexNode.toString().contains("switch_out")) {
//								end = cVexNode.getSnumber();
//							}
//						}
//
//						for (VexNode cVexNode : graph.getAllnodes()) {
//
//							int num = cVexNode.getSnumber();
//							if (cVexNode.toString().contains("stmt") && num > start && num < end) {
//								for (NameOccurrence cNameOccurrence : cVexNode.getOccurrences()) {
//									if (cNameOccurrence.toString().split(":")[0].equals(occ.toString().split(":")[0])) {
//										DepGraphNode g2 = g.addChild(cNameOccurrence);
//										dfs(cNameOccurrence, g2, cond, depth + 1);
//									}
//								}
//							}
//						}
//
//					}
//					// add by lsc 2018/12/6��
//					// ����˳��ִ�еĳ���ŵ���else��֧��,�����������Դ�����ٸ���ʦ̽��һ��
//					// ��������׷�ݵ�switch�ڣ��򲻼���switch�ڴ�����ֻ����switch֮�µ��Լ�switch����Լ������֮�ϵ�(����)
//					else {
//
//						// �����е��ս������ǰ�Ķ���ɾ��������int b = a; b ++ ; b = 2 ; n = b;
//						// ��ʱֻ��Ҫ������b=2����
//						List<NameOccurrence> def1 = occ.getUse_def();
//						Collections.sort(def1, new Comparator<NameOccurrence>() {
//							@Override
//							public int compare(NameOccurrence o1, NameOccurrence o2) {
//								int b = Integer.parseInt(o1.toString().split(":")[1]);
//								int a = Integer.parseInt(o2.toString().split(":")[1]);
//								return a > b ? 1 : (a == b ? 0 : -1);
//							}
//						});
//						// ��ÿ��Ե��ﱾʹ�ó��ֵ����ж������
//						List<NameOccurrence> def = new ArrayList<>();
//						for (NameOccurrence nameOccurrence : def1) {
//							def.add(nameOccurrence);
//							SimpleNode simpleNode = (SimpleNode) nameOccurrence.getLocation().jjtGetParent();
//							
//							System.err.println(nameOccurrence+"2018/12/12"+simpleNode.getOperators());
//						
//							boolean f1 = isDefOfConstant(nameOccurrence);
//							int count = simpleNode.jjtGetNumChildren();
//							boolean f2 = simpleNode.jjtGetNumChildren() == 1;
//							
//							
//							if(simpleNode.jjtGetNumChildren() != 1) {
//								List<NameOccurrence>def2 = nameOccurrence.getUndef_def();
//								if(def2 != null) {
//									for(NameOccurrence o : def2) {
//										DepGraphNode g2 = g.addChild(o);
//										dfs(o, g2, cond, depth + 1);
//									}
//								}
//							}
//							
//							if (isDefOfConstant(nameOccurrence) ) {
//								break;
//							}
//						}
//
//						//
//						for (NameOccurrence o : def) {
//
//							DepGraphNode g2 = g.addChild(o);
//
//							VexNode from = o.getLocation().getCurrentVexNode();
//							VexNode to = occ.getLocation().getCurrentVexNode();
//							List<VexNode> pList = Graph.findAPath(from, to);
//
//							// add by lsc 2018/9/25����������֧
//							// ΪʲôpList.size-1 ?
//							for (int i = 0; i < pList.size(); i++) {
//
//								VexNode a = pList.get(i);
//
//								// add test by lsc,�����������Դ�Ϊͻ�ƿڴ���if-else��֧
//								// System.out.println("test2018/10/9:"+a.toString()
//								// +a.getOccurrences().toString());
//
//								if (a.toString().contains("if_head")) {
//									for (VexNode nVexNode : pList) {
//										ValueSet valueSet = vexNode.getLastvalueset();
//										System.out.println(valueSet);
//										SymbolDomainSet symbolDomainSet = vexNode.getLastsymboldomainset();
//										System.out.println(symbolDomainSet);
//										// System.out.println(nVexNode.falsetag
//										// +
//										// "*******************" + nVexNode);
//									}
//									System.out.println("vexNode: " + a);
//
//									SimpleNode simpleNode = a.getTreenode();
//									System.out.println(simpleNode + ":" + simpleNode.getImage() + " ��ʼ�У�"
//											+ simpleNode.getBeginLine() + " ������" + simpleNode.getEndLine());
//
//									System.out.println("USE++++++++++++++++++++++++++++++++++++++" + o + " to " + occ
//											+ "   Ŀǰ����" + ": " + occ + "��use_def:" + occ.getUse_def());
//									System.out.println("�˽ڵ�ı�����" + a.getOccurrences() + " �˽ڵ������use_def "
//											+ a.getOccurrences().get(0).getUse_def());
//									for (NameOccurrence o1 : a.getOccurrences()) {
//										DepGraphNode g3 = g.addChild(o1);
//										dfs(o1, g3, 1, depth + 1);
//									}
//								}
//							}
//
//							dfs(o, g2, cond, depth + 1);
//						}
//
//					}
//
//				}
//
//				// if (def == null || def.size() == 0) {
//				// // �޶���㣬������ȫ��
//				// Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
//				// // ���ͼ
//				// String funcname = cfgmap2.get(cfg); // ��ȡ��ǰ�������ں����ĺ�����
//				//
//				// InterCallGraph callGraph = InterCallGraph.getInstance();
//				//
//				// MethodNode curMNode = null;
//				// for (MethodNode mn : callGraph.getINTERMETHOD()) {
//				// Method m = mn.getMethod();
//				// if (m.getName().equals(funcname)) {
//				// curMNode = mn;
//				// break;
//				// }
//				// }
//				//
//				// // add by lsc 2018/10/24
//				// System.out.println("curMNode: " + curMNode.getMethod() + " "
//				// + "�������֣� " + occ.toString()
//				// + " " + "�������ͣ� " + occ.getOccurrenceType());
//				//
//				// if (curMNode != null) {
//				// Map<Position, ArrayList<SCVPString>> callerInfo =
//				// curMNode.getMethod().getCallerInfo();
//				// if (callerInfo == null || callerInfo.size() == 0) {
//				// List<Method> callers = new ArrayList<>();// curMNode�ĵ�����
//				// for (MethodNode mn : callGraph.getINTERMETHOD()) {
//				// for (MethodNode mn2 : mn.getCalls()) {
//				// if (mn2 == curMNode) {
//				// callers.add(mn.getMethod());
//				// }
//				// }
//				// }
//				//
//				// for (Method caller : callers) {
//				// Map<String, List<SCVPString>> ext =
//				// caller.getExternalEffects();
//				// for (String occstr : ext.keySet()) {
//				// SCVPString value = ext.get(occstr).get(0);// ����ֻ��1��
//				// String occName = occ.toString().split(":")[0];
//				// String occName1 = occstr.split(":")[0];
//				// if (occName.equals(occName1)) {
//				// String fileName = value.getPosition().getfileName();
//				// String funcName = value.getPosition().getFunctionName();
//				// String symbolName = occName1;
//				// int line2 = Integer.valueOf(occstr.split(":")[1]);
//				// NameOccurrence next = locate(fileName, funcName, symbolName,
//				// line2);
//				// if (next != null) {
//				// DepGraphNode g4 = g.addChild(next);
//				// dfs(next, g4, cond, depth + 1);
//				// }
//				// }
//				// }
//				// }
//				// } else {
//				// for (List<SCVPString> val : callerInfo.values()) {
//				// SCVPString scvp = val.get(0);
//				// for (String nextocc : scvp.getOccs()) {
//				// String fileName = scvp.getPosition().getfileName();
//				// String funcName = scvp.getPosition().getFunctionName();
//				// String symbolName = nextocc.split(":")[0];
//				// int line2 = Integer.valueOf(nextocc.split(":")[1]);
//				// NameOccurrence next = locate(fileName, funcName, symbolName,
//				// line2);
//				// if (next != null) {
//				// DepGraphNode g5 = g.addChild(next);
//				// dfs(next, g5, cond, depth + 1);
//				// }
//				// }
//				// }
//				// }
//				// }
//				//
//				// }
//			} else if (occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE) { // ʹ�ú���
//																					// i++
//																					// ,i+=2��
//
//				// add by lsc 2018/11/23
//				SimpleNode node = occ.getLocation();
//				List<NameOccurrence> def = new ArrayList<>();
//				if (occ.isSelfAssignment()) {
//					List<NameOccurrence> def1 = occ.getUse_def();
//					for (NameOccurrence occurrence : def1) {
//						def.addAll(occurrence.getUndef_def());
//					}
//					if (def.size() == 0) {
//						System.out.println("]]]]]]]]]]]]]]]]]]]]]]]]]]]" + occ.toString());
//					}
//				} else {
//					def = occ.getUse_def();
//				}
//
//				for (NameOccurrence o : def) {
//					DepGraphNode g2 = g.addChild(o);
//					//
//					// VexNode from = o.getLocation().getCurrentVexNode();
//					// VexNode to = occ.getLocation().getCurrentVexNode();
//					// List<VexNode> pList = Graph.findAPath(from, to);
//					// for (int i = 0; i < pList.size(); i++) {
//					// VexNode a = pList.get(i);
//					// if (a.toString().contains("if_head")) {
//					// System.out.println("DEF_AFTER_USE++++++++++++++++++++++++++++++++++++++++++");
//					// for (NameOccurrence o1 : a.getOccurrences()) {
//					// DepGraphNode g3 = g.addChild(o1);
//					// dfs(o1, g3, 1, depth + 1);
//					// }
//					// }
//					// }
//					//
//					dfs(o, g2, cond, depth + 1);
//				}
//			} else if (occ.getOccurrenceType() == OccurrenceType.DEF) {
//
//				// add by lsc 2018/11/23 �����a = a + 1;���ܼ�����ǰ��Դ���������
//				if (occ.isAssignSameVar(occ.getLocation())) {
//
//					// �ⲿ�� �����a = a + 1;���ܼ�����ǰ��Դ���������
//					List<NameOccurrence> def = occ.getUndef_def();
//
//					for (NameOccurrence o : def) {
//						DepGraphNode g2 = g.addChild(o);
//
//						dfs(o, g2, cond, depth + 1);
//					}
//
//					// add by lsc 2018/12/4 �ⲿ�ֽ����b = b + a���⣬��������������a�ļ�����Դ
//
//					VexNode vexNode2 = occ.getLocation().getCurrentVexNode();
//					for (NameOccurrence nameOccurrence : vexNode2.getOccurrences()) {
//						if (nameOccurrence.getImage() != occ.getImage()) {
//							DepGraphNode g2 = g.addChild(nameOccurrence);
//							dfs(nameOccurrence, g2, cond, depth + 1);
//						}
//					}
//
//				} else {
//
//					// add by lsc 2018/11/25����� a += 2������
//					if (isSelfAssignmentChange(occ, list_operator)) {
//
//						List<NameOccurrence> def = occ.getUndef_def();
//
//						for (NameOccurrence o : def) {
//							DepGraphNode g2 = g.addChild(o);
//							//
//							// VexNode from =
//							// o.getLocation().getCurrentVexNode();
//							// VexNode to =
//							// occ.getLocation().getCurrentVexNode();
//							// List<VexNode> pList = Graph.findAPath(from, to);
//							// for (int i = 0; i < pList.size(); i++) {
//							// VexNode a = pList.get(i);
//							// if (a.toString().contains("if_head")) {
//							// System.out.println("DEF2++++++++++++++++++++++++++++++++++++++");
//							// for (NameOccurrence o1 : a.getOccurrences()) {
//							// DepGraphNode g3 = g.addChild(o1);
//							// dfs(o1, g3, 1, depth + 1);
//							// }
//							// }
//							// }
//							//
//							dfs(o, g2, cond, depth + 1);
//						}
//					}
//
//					SCVPString scvp = occ.getSCVP();
//					List<String> vlist = scvp.getOccs();
//					
////					//add by lsc 2018/12/11,Ϊ�˽����������,��δ���
////					if(vlist.isEmpty()) {
////						VexNode cVexNode = occ.getLocation().getCurrentVexNode();
////						System.err.println(cVexNode.getOccurrences()+"lsclsc");
////						System.err.println(occ.getLocation()+" "+ occ);
////						
////						//ȡ���Ҳ�������б����get�������޸��ˣ�pri->post,��ʱ�Ļ���
////						List rightVars = getRightVar(occ.getLocation());
////						System.out.println(rightVars.toString()+"pppppppppppp");
////						
////						for(Object o:rightVars)
////			    		{
////			    			if(o instanceof ASTPostfixExpression)
////			    			{
////			    				ASTPostfixExpression priExp=(ASTPostfixExpression) o;
////			    			
////			    				
////			    				ASTFunctionDefinition astFunctionDefinition = (ASTFunctionDefinition) priExp.getFirstParentOfType(ASTFunctionDefinition.class);
////			    				String funcName = astFunctionDefinition.getImage();
////			    				
////			    				System.out.println(args[1]+" "+funcName+" " +priExp.getImage()+"  "+priExp.getBeginLine()+"lsc");
////			    				
////			    				NameOccurrence nameOccurrence = locate(args[1], funcName, priExp.getImage(), priExp.getBeginLine());
////			    				System.out.println(nameOccurrence + " this");;
////			    				DepGraphNode g2 = g.addChild(nameOccurrence);
////								dfs(nameOccurrence, g2, cond, depth + 1);
////			    			}
////			    		}
////						
////						
////
////					}
//					
//
//					// add test by lsc 2018/10/9
//					System.out.println("test2018/10:" + vlist.toString());
//
//					for (String v : vlist) {
//						Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
//						NameOccurrence o = cfg.getOcctable().get(v);
//						if (o.getImage().toString().equals(occ.getImage()))
//							continue;
//						DepGraphNode g2 = g.addChild(o);
//						//
//						// VexNode from = o.getLocation().getCurrentVexNode();
//						// VexNode to = occ.getLocation().getCurrentVexNode();
//						// List<VexNode> pList = Graph.findAPath(from, to);
//						// for (int i = 0; i < pList.size(); i++) {
//						// VexNode a = pList.get(i);
//						// if (a.toString().contains("if_head")) {
//						// System.out.println("DEF3++++++++++++++++++++++++++++++++++++++");
//						// for (NameOccurrence o1 : a.getOccurrences()) {
//						// DepGraphNode g3 = g.addChild(o1);
//						// // if (cond==0) {
//						// // cond=1;
//						// // System.out.println(o + "," + g);
//						// // }
//						// dfs(o1, g3, 1, depth + 1);
//						// }
//						// }
//						// }
//						//
//						dfs(o, g2, cond, depth + 1);
//					}
//					String s = scvp.getStructure();
//
//					System.out.println("s" + s + "==============================================================");
//					if (s.contains("Function:")) { // ����ֵ
//						int id = s.indexOf("Function");
//						s = s.substring(id);
//						String[] fs = s.trim().split("Function:");
//
//						for (String string : fs)
//							System.out.println("�������ƣ�" + string
//									+ "==============================================================");
//
//						ASTStatement statement = (ASTStatement) occ.getLocation()
//								.getFirstParentOfType(ASTStatement.class);
//
//						System.out.println("statement:" + statement
//								+ "==============================================================");
//
//						List<Node> priList = statement.findChildrenOfType(ASTPrimaryExpression.class);
//						System.out.println(
//								"priList" + priList + "==============================================================");
//						for (String f : fs) {
//							for (Node n : priList) {
//								ASTPrimaryExpression pri = (ASTPrimaryExpression) n;
//								if (pri.isMethod() && pri.getImage().equals(f)) {
//									// 2011.6.24
//									// Ŀǰ��δ��������⣺����Ǻ���ָ����ʽ�ĺ������ã���λ�ȡ��ȷ�ĺ������ã�
//
//									System.out.println(pri.getMethodDecl()
//											+ "==============================================================");
//									if (pri.getMethodDecl() == null)
//										continue;
//									Method m = pri.getMethodDecl().getMethod();
//									System.out.println("Method:" + m
//											+ "==============================================================");
//									SimpleNode entNode = pri.getMethodDecl().getMethodNameDeclaratorNode();
//									System.out.println("entNode: " + entNode
//											+ "==============================================================");
//									Graph cfg = null;
//									if (entNode instanceof ASTFunctionDefinition)
//										cfg = ((ASTFunctionDefinition) entNode).getGraph();
//									List<SCVPString> ret = m.getReturnList();
//									System.out.println("m.getReturnList:" + ret.toString()
//											+ "==============================================================");
//									for (SCVPString scvpString : ret) {
//										for (String v : scvpString.getOccs()) {
//											if (cfg != null) {
//												NameOccurrence o = cfg.occtable.get(v);
//												DepGraphNode g2 = g.addChild(o);
//												dfs(o, g2, cond, depth + 1);
//											}
//										}
//									}
//								}
//							}
//						}
//					}
//				}
//
//			} else if (occ.getOccurrenceType() == OccurrenceType.ENTRANCE) {
//				// ��÷����������﷨���ڵ�,(֮����Լ�ӻ�ȡ�������������Ϣ)
//				ASTFunctionDefinition funcdef = (ASTFunctionDefinition) occ.getLocation()
//						.getFirstParentOfType(ASTFunctionDefinition.class);
//
//				// add test by lsc 2018/11/26
//				// ����˲�����������ȷ�����⣬ԭ������������ȡ��ʽ��������(���ܱ�֤funcdef.getScope()�Ĳ��������µĴ������������﷨������֤��ȷ).
//				String[] ParameterList = new String[funcdef.getParameterCount()];
//				int count = 0;
//				System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
//				System.out.println(funcdef.getImage());
//				List<SimpleNode> list = funcdef.findXpath(".//ParameterDeclaration");
//				for (SimpleNode simpleNode : list) {
//					List<SimpleNode> list2 = simpleNode.findXpath(".//Declarator");
//					for (SimpleNode simpleNode2 : list2) {
//						System.out.println(simpleNode2.getImage() + ":" + simpleNode2.getBeginColumn());
//						ParameterList[count++] = simpleNode2.getImage();
//					}
//				}
//
//				System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
//
//				int index = 0;
//				// boolean isFind = false; //�ж��Ƿ��ҵ�
//
//				System.out.println("��ǰ����" + occ.toString().split(":")[0]);
//
//				for (int i = 0; i < count; i++) {
//					if (occ.toString().split(":")[0].equals(ParameterList[i])) {
//						index = i + 1;
//						break;
//					}
//				}
//
//				System.out.println("�ó��˱�����" + occ.toString().split(":")[0] + "��indexΪ:" + index);
//
//				if (funcdef != null) {
//					// ��һ��HashMap����¼ǰ��ժҪ�����������ú����������⣬������������Դ����
//					// �Ҿ�����Ҫ���һ������������index���������ֵ�����Դ�ĸ����� 2018/9/27 lsc
//					HashMap<Position, ArrayList<SCVPString>> callerInfo = funcdef.getDecl().getMethod().getCallerInfo();
//					for (Position p : callerInfo.keySet()) {
//						// add by lsc 2018/9/27
//
//						// System.out.println("test:" + index);
//
//						// System.out.println("test��" + p.toString());
//						// System.out.println("scvpstring :" +
//						// callerInfo.get(p).toString());
//
//						Graph cfg = cfgmap.get(p.getFunctionName());
//						if (cfg != null) {
//							for (SCVPString scvp : callerInfo.get(p)) {
//
//								String fileName = p.getFileName();
//								String funcName = p.getFunctionName();
//								String symbolName = scvp.getVar();
//
//								// add test by lsc
//								// System.out.println("test:" + symbolName);
//								// System.out.println("index:" + p.getIndex());
//								int line1 = p.getBeginLine();
//
//								// ���ڶԱȲ����������о�ȷ��Դ add by lsc 2018/10/9
//								if (p.getIndex() == index) {
//									System.out.println("�к�:" + line1 + "  ������ " + symbolName + "  ������" + index);
//									NameOccurrence occ2 = locate(fileName, funcName, symbolName, line1);
//									System.out.println("occ2���ݣ�" + occ.toString());
//
//									if (occ2 == null)
//										continue;
//									DepGraphNode g3 = g.addChild(occ2);
//									dfs(occ2, g3, cond, depth + 1);
//
//									for (String v : scvp.getOccs()) {
//
//										System.out.println(scvp.getOccs() + "lsc");
//
//										NameOccurrence o = cfg.occtable.get(v);
//										DepGraphNode g2 = g.addChild(o);
//										dfs(o, g2, cond, depth + 1);
//									}
//
//								}
//
//							}
//						}
//					}
//				}
//			}
//		} catch (Exception e) {
//			e.printStackTrace();
//		}

//	}

	
	 /**
     * add by lsc 2018/12/7��Ϊ���ж���������Ƿ�λ�ڵȺ����
     * @return �жϵ�ǰ�������֣�NameOccurence)�Ƿ�λ�ڣ���࣬���Ƿ�Ϊ������ֵDEF
     */
    public boolean isOnLeftHandSideForArray(NameOccurrence occ) {
    	SimpleNode declarator=null;
       
    	if(occ.getLocation() instanceof ASTDirectDeclarator) {
    		return true;
    	}
    	
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
        	//add else branch by cmershen,2016.5.31 ��Ӷ�*p=2���͵�֧��
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
		
		//add by lsc 2018/12/11����ֱ�Ӷ����ʱ������int m = a + 1;
		if(node instanceof ASTDirectDeclarator) {
			ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) node.getFirstParentOfType(ASTInitDeclarator.class);
			ASTInitializer astInitializer = (ASTInitializer) astInitDeclarator.getFirstChildOfType(ASTInitializer.class);
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
					// List<NameOccurrence>list = vexNode2.getOccurrences();
					// for(NameOccurrence nameOccurrence : list) {
					// for(NameOccurrence nameOccurrence2 :
					// nameOccurrence.getUse_def()) {
					// System.out.println("switch����������ǰ������������﷨���ڵ�:"+nameOccurrence2.getLocation());
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
					// System.out.println("switch����������ǰ��������Ƿ��ǳ�����ֵ�� "+flag);
					// System.out.println("switch����������ǰ������ֵ��"+nameOccurrence2.getSCVP());
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
		// �ⲿ����Դ��ȡ
		// �����vexNode�ڵ���Ϣ 2018/11/29
		for (Entry<VexNode, List<String>> entry : map_line_list_out_variable.entrySet()) {
			VexNode vexNode = entry.getKey();
			List<String> list = entry.getValue();
			list.add(vexNode.toString());
			list_out_variable.add(list);
		}
		System.out.println("����������ص��ⲿ����Դ�� ");
		System.out.println("list_out_variable: " + list_out_variable);

		System.out.println("����ڵ����Ӧ������ص��ⲿ����Դ��ӳ�䣺");
		System.out.println("������ " + map_line_list_out_variable.size());
		for (Entry<VexNode, List<String>> entry : map_line_list_out_variable.entrySet()) {
			VexNode vexNode = entry.getKey();
			List<String> list = entry.getValue();
			System.out.println(vexNode + " " + list);
		}
		return list_out_variable;
	}

	public HashSet<String> analyse3() throws Exception {

		SearchFunction searchFunction = new SearchFunction();
		searchFunction.main(args);
		list_function = searchFunction.getList();
		// System.out.println(list_function.toString());
		map_function = searchFunction.getMapOfFunction();
		map_function_contains = searchFunction.getMapOfFunctionContains();

		getpathSet3(args[2], args[2]);

		System.out.println("������������õ����·������Դ�����");
		// System.out.println(pathSet3);

		// System.out.println("��Դ·�������������Ƕ����ӳ��:");
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
		// //����HightlightFunction
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
		// System.out.println("���HighlightFunction:");
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

}
