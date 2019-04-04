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
import softtest.ast.c.ASTLogicalANDExpression;
import softtest.ast.c.ASTNestedFunctionDefinition;
import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTUnaryOperator;
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

public class DepchainHome implements Serializable {
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

	public DepchainHome(String[] args) {

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

	// add by lsc 2019/3/1
	public List<List<String>> global_VariablesList = new ArrayList<>();
	
	//add by lsc 2019/4/2 ���ڼ�¼�ź���׷��
	public List<String> Semaphore_tracking = new ArrayList<>();     
	
	//add by lsc 2019/4/2���ڼ�¼���еĿ�����������
	public List<String> controList = new ArrayList<>();
	
 	//�¼� ywj  4/3 ��¼�����ڶ�ȫ�ֱ����Ĳ���
	public HashMap<String, List<Map<VexNode, String>>> global_func = new HashMap<>();

	public static void main(String[] args) throws Exception {
		DepchainHome test = new DepchainHome(args);
		System.out.println("�ⲿ����Դ��");
		
		test.prepare();
		System.out.println(test.analyse1());// ���������
		
		System.out.println("list_out : " + test.list_out);
		
		

		System.out.println(test.analyse2());// ���������
	

		test.analyse3();
		System.out.println("pathSet3: " + test.pathSet3);
		
		//add by lsc 2019/1/2 ���ڻ�ȡ�������������Ӧ�����﷨���ڵ��ӳ�䣬�Լ������������Ӧ�ļ���ӳ��
//		for(Map.Entry<String, String> entry : test.map_function_path.entrySet()) {
//			System.err.println("mmmm"+entry.getKey()+":"+entry.getValue()+ ":" +test.map_function_simpleNode.get(entry.getKey()).getBeginLine());
//		}
		
	

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
		for(Map.Entry<String, List<String>>entry : test.map_function_internal.entrySet()) {
			System.out.println(entry.getKey()+":"+entry.getValue());
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

		// for(Entry<String, List<String>> entry :
		// map_function_internal.entrySet()) {
		// System.out.println(entry.getKey()+":" + entry.getValue());
		// }

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
	
	public void prepare() throws IOException {
		process();
		
		
		
		getMap_function(cgMap);
		getMap_function_contains(cgMap);
		getList_function(cgMap);
		getMap_function_path(cgMap);
		getMap_function_simpleNode(cgMap);
		
		
		getReservedWords();
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
public HashSet<String> analyse3() throws Exception {

		
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

public HashSet<String> pathSet3 = new HashSet<String>();

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

			include.add("C:\\Program Files (x86)\\DTS\\DTS\\DTSGCC\\include\\stdio");
			
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
				 * add by lsc 2018/9/14�˴��ȽϹؼ��ĵ�����ASTTranslationUnit.java�е� public Object
				 * jjtAccept(CParserVisitor visitor, Object data) ����
				 * DUAnalysisVisitor.java�е�visit������ ֮��initDefUse(),��֮��AbstractScope.java�е�
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
	
	
	
	
	/**
	 * add by lsc 2019/3/12
	 * ��ȡ�������������Ӧ�ĳ����﷨���ڵ��ӳ��
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
	 * ��ȡ������������λ�õ�ӳ��
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
	 * ��ȡ�����Զ���ķ������б�
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
	 * ��ȡ�������䱻���ú�����ӳ��
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
	 * add by lsc 2019/3/17
	 * ��ȡ����������ú�����ӳ��
	 */
	public void getMap_function_contains(HashMap<String, CGraph> cgMap) {
		//add test by lsc 2019/3/12
		for(String fString : files) {
			CGraph g = cgMap.get(fString);
			Hashtable<String, CEdge>hashtable = g.edges;
			Set<String> set = hashtable.keySet();
			for(String string : set ) {
				CEdge edge = hashtable.get(string);
				String start = edge.getTailNode().getMethodDeclaration().getImage();
				String end = edge.getHeadNode().getMethodDeclaration().getImage();
			
				if(!map_function_contains.containsKey(start)) {
					List<String> list = new ArrayList<>();
					list.add(end);
					map_function_contains.put(start, list);
				}
				else {
					List<String> list = map_function_contains.get(start);
					list.add(end);
					map_function_contains.put(start, list);
				}
				
				
			}
		
			
		}
		System.out.println("map_function_contains : "+ map_function_contains);
	}
	
	
	

	// ȫ�ֱ���map2�д洢��ÿ�������������Դ����к�
	private Map<String, Set<Integer>> map2 = new HashMap<>();

	// add by lsc 2019/3/1
	List<List<VexNode>> paths = new ArrayList<>();

	public Map<String, Set<Integer>> analyse2() throws Exception {
//		findAstOfVariable findAstOfVariable = new findAstOfVariable();
//		findAstOfVariable.main(args);
//		list_operator = findAstOfVariable.getList_Operator();
//
//		System.out.println(list_operator.toString());
//		prepare();
	
		
		
		System.out.println("���ܵ���������⺯�����ϣ� " + list_outsource);

		System.out.println("�����Զ���ĺ���list_function: " + list_function);

		// add by lsc 2019/1/11
		String funcName = args[2];
		String varName = args[3];
		int line = Integer.parseInt(args[4]);
		
		SimpleNode treeNode = getSimpleNodeOflocate(funcName,  1,  varName,line);
		VexNode vexNode1 = treeNode.getCurrentVexNode();
		for(VexNode vexNode : vexNode1.getGraph().getAllnodes()) {
			System.out.println("today : " + vexNode.getTreenode().getBeginLine());
		}
		
		VexNode vexNode = getVexNodeOflocate(funcName, varName, line);
		System.out.println(VexNodeType.getVexNodeType(vexNode, list_outsource));
		System.out.println(getVexNodeType(vexNode));

		// ��ÿ���ڵ��ǰ���ڵ�
		getVexNodeOfPreMap(vexNode);

		/*
		 * add by lsc 201
		 */
		set_path_node.clear();
		paths.clear();
//		paths = getAllPathNew(vexNode, paths);

		
		paths = findpathNew(new ArrayList<VexNode>(), vexNode, paths);
		System.err.println("paths : ");
		for (List<VexNode> tempList : paths) {
			System.err.println(tempList);
		}
		System.err.println("set_path_node: " + set_path_node.toString());
		System.err.println("paths��Ԫ�ظ���Ϊ: " + paths.size());
		System.err.println("set��Ԫ�ظ���Ϊ: " + set_path_node.size());

		System.out.println("�����ڵ������Ϊ�� " + getVarType(vexNode, varName, Integer.parseInt(args[5])));
	
		
		System.out.println("�ź���׷������� �� " + Semaphore_tracking);
		System.out.println("���еĿ��Ʊ��� �� " + controList);
		
		
		
		//test 2019/3/13 ����
//		for(VexNode vexNode2  : vexNode.getGraph().getAllnodes()) {
//			if(getVexNodeType(vexNode2).contains("2") ||getVexNodeType(vexNode2).contains("4") ) {
//				List<SimpleNode> list = getASTUnaryExpression(vexNode2);
//				int count = 0;
//				for(SimpleNode node : list) {
//					if(count == 0) {
//						count ++;
//						continue;
//					}
////					System.out.println(vexNode2.getTreenode().getBeginLine());
////					System.err.println(list);
//					ASTUnaryExpression astUnaryExpression = (ASTUnaryExpression) node;
//					System.out.println(astUnaryExpression + "   "+ astUnaryExpression.getImage() + "    "+ astUnaryExpression.getBeginLine() + "simpNode :" + node.getImage());
//				}
//				System.out.println();
//				System.out.println();
//			}
//		}
		
		

		// ��ȡȫ�ֱ�������Ϣ
		// add by lsc 2019/3/1
		global_VariablesList = getGlobaVariables();

//		//�ڵ��������
//		String string = paths.get(0);
//		List<String> list = new ArrayList<>();
//		list.add(args[2]);
//		vexnode_Analysis(string , list);
		FunctionGlobalVarivable fu = new FunctionGlobalVarivable();
		//������list_out
		global_func = fu.getAllGlobalChange(list_outsource, files, astmap, list_function, cfgmap);
		dfs(vexNode, funcName, varName , 1);
		System.out.println("map2�е�������111111�� "+map2);
		return map2;
	}
	
	public Map<String, Set<Integer>> vexnode_Analysis(String string, List<String> list) {

		return map2;
	}

	/**
	 * add by lsc 2019/3/1 Ϊ�˻�ȡ���е�ȫ�ֱ�������Ϣ
	 * 
	 * @return
	 */
	public List<List<String>> getGlobaVariables() {

		// ��ӡ�﷨��
		for (String string : files) {

			ASTTranslationUnit rooTranslationUnit = astmap.get(string);
			System.err.println(rooTranslationUnit);

			List<SimpleNode> list = rooTranslationUnit.findXpath(".//ExternalDeclaration/Declaration");
			int count = 0;
			for (SimpleNode astDeclarator : list) {
				if (count == 0) {
					count++;
					continue;
				}
				List<SimpleNode> listTreeNodeList = astDeclarator.findXpath(".//DirectDeclarator");
				for (SimpleNode node : listTreeNodeList) {
					ASTDirectDeclarator astDirectDeclarator = (ASTDirectDeclarator) node;
					List<String> list2 = new ArrayList<>();

					String fileString = string;

					String varString = astDirectDeclarator.getImage();
					int row = astDirectDeclarator.getBeginLine();

					list2.add(string);
					list2.add(varString);
					list2.add(String.valueOf(row));
					global_VariablesList.add(list2);
				}

			}

		}
		System.out.println("ȫ�ֱ�������ϢΪ�� " + global_VariablesList);
		return global_VariablesList;
	}

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
	 * add by lsc 2019/1/22 ���ݵ�ǰ�����õ���ǰ������ͼ�Ͻڵ�������ڵ��mapӳ��
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
			System.out.println("�ڵ����ǰ���ڵ��ӳ�䣺" + node + "   :    " + list + "     :    " + node.getTreenode()
					+ "    :    " + getVexNodeType(node));
		}
		return map;
	}

	// add by lsc 2019/1/15�����洢�Ѿ������ʹ��Ľڵ�
	Set<VexNode> set_path_node = new HashSet<>();

	/*
	 * add by lsc 2019/3/1 * �������� ��Ŀ��ڵ��������ǰ·�� ���ܣ�����Ŀ��ڵ��ȡ�Ӻ�����ڵ�������пɴ�·��
	 */
	public List<List<VexNode>> getAllPathNew(VexNode vexNode, List<List<VexNode>> path) {
		if (paths.isEmpty()) {
			findpathNew(new ArrayList<VexNode>(), vexNode);
		}
		return path;
	}

	/*
	 * add by lsc 2019/1/16 ��20:32
	 */
	public void findpathNew(List<VexNode> oldpath, VexNode newVexNode) {
		if (!oldpath.contains(newVexNode)) {
			oldpath.add(newVexNode);
			set_path_node.add(newVexNode);
		}
		Hashtable<String, Edge> hashtable = newVexNode.getInedges();
		if (hashtable.isEmpty()) {
			paths.add(new ArrayList<>(oldpath));
		} else {
			Set<String> set = hashtable.keySet();
			for (String string : set) {
				Edge edge = hashtable.get(string);
				VexNode vexNode = edge.getTailNode();
				if (!set_path_node.contains(vexNode) || !oldpath.contains(vexNode)) {
					findpathNew(new ArrayList<>(oldpath), vexNode);
				} else if (set_path_node.contains(vexNode) && oldpath.contains(vexNode)) {
					if (vexNode.toString().contains("for_head") || vexNode.toString().contains("while_head")) {
						oldpath.add(vexNode);
						Hashtable<String, Edge> table = vexNode.getInedges();
						Set<String> set_table = table.keySet();
						for (String string2 : set_table) {
							Edge edge2 = table.get(string2);
							VexNode vexNode2 = edge2.getTailNode();
							if (vexNode2.getSnumber() < vexNode.getSnumber()) {
								findpathNew(new ArrayList<>(oldpath), vexNode2);
							}
						}
					}
				}
			}
		}
	}

	/**
	 * 
	 * add by lsc 2019/3/4
	 */
	public List<List<VexNode>> findpathNew(List<VexNode> oldpath, VexNode newVexNode, List<List<VexNode>> paths) {

		if (!oldpath.contains(newVexNode.toString())) {
			oldpath.add(newVexNode);
			set_path_node.add(newVexNode);
		}
		Hashtable<String, Edge> hashtable = newVexNode.getInedges();
		if (hashtable.isEmpty()) {
			paths.add(new ArrayList<>(oldpath));
		} else {
			Set<String> set = hashtable.keySet();
			for (String string : set) {
				Edge edge = hashtable.get(string);
				VexNode vexNode = edge.getTailNode();
				if (!set_path_node.contains(vexNode) || !oldpath.contains(vexNode)) {
					findpathNew(new ArrayList<>(oldpath), vexNode, paths);
				} else if (set_path_node.contains(vexNode) && oldpath.contains(vexNode)) {
					if (vexNode.toString().contains("for_head") || vexNode.toString().contains("while_head")) {
						oldpath.add(vexNode);
						Hashtable<String, Edge> table = vexNode.getInedges();
						Set<String> set_table = table.keySet();
						for (String string2 : set_table) {
							Edge edge2 = table.get(string2);
							VexNode vexNode2 = edge2.getTailNode();
							if (vexNode2.getSnumber() < vexNode.getSnumber()) {
								findpathNew(new ArrayList<>(oldpath), vexNode2, paths);
							}
						}
					}
				}
			}
		}
		return paths;
	}

	public void setArgs(String[] args) {
		this.args = args;
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
			System.err.println(temp.getBeginLine() +"   " + vexNode);
			if (temp.getBeginLine() == line) {
				return vexNode;
			}
		}
		return null;
	}

	/**
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

	/**
	 *
	 * �Կ������ڵ����ͽ����ж� type == 0 ������ͼ��ڽڵ� 
	 * type == 1 ֻ�к��� f()����f(c) 
	 * type == 2 �ж������� �� ����int c = m + f(); 
	 * type == 3 �ж�������(����������δ��ֵ) , ����int c; 
	 * type == 4 �޶������� �� ���� c = m + a; 
	 * type == 5 ������ͼ���ڽڵ� 
	 * type == 6 �⺯�� 
	 * type == 7 ������� ����c ++ 
	 * type == 8�����ݽڵ�
	 * type == 9return�ڵ�
	 */
	public String getVexNodeType(VexNode vexNode) {
		SimpleNode treeNode = vexNode.getTreenode();
		String type = "8_�����ݽڵ�";
		if (vexNode.getOutedges().isEmpty()) {
			type = "5_������ͼ���ڽڵ�";
		} else if (vexNode.getInedges().isEmpty()) {
			type = "0_������ͼ��ڽڵ�";
		} else {
			if (treeNode.toString().equals("Declaration")) {
				ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) treeNode
						.getFirstChildOfType(ASTInitDeclarator.class);
				if (astInitDeclarator.jjtGetNumChildren() == 1) {
					type = "3_�ж�������(��������,δ��ֵ)";
				} else if (astInitDeclarator.jjtGetNumChildren() == 2) {
					type = "2_�ж�������";
				}

			} else if (treeNode.toString().equals("ExpressionStatement")) {
				ASTAssignmentExpression assignmentExpression = (ASTAssignmentExpression) treeNode
						.getFirstChildOfType(ASTAssignmentExpression.class);
				if (assignmentExpression.jjtGetNumChildren() == 1) {
					ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression) assignmentExpression
							.getFirstChildOfType(ASTPrimaryExpression.class);
					if (astPrimaryExpression.isMethod()) {
						if (list_outsource.contains(astPrimaryExpression.getImage())) {
							type = "6_�⺯��";
						} else {
							type = "1_ֻ�к���f()����f(c)";
						}
					} else {
						type = "7_�����Լ����� ����c ++";
					}
				} else if (assignmentExpression.jjtGetNumChildren() == 3) {
					type = "4_�޶�������";
				}
			}
			else if(vexNode.toString().contains("return")) {
				type = "9_return�ڵ�";
			}
		}
		return type;
	}

	/**
	 * �жϱ����ĳ������� add by lsc 2019/2/15 ����3��:�������ڿ������ڵ�vexNode�� ������varName , ���� index
	 */
	public String getVarType(VexNode vexNode, String varName, int index) {
		String type = "";
		String string = getVexNodeType(vexNode).split("_")[0];
		if (string.equals("0")) {
			SimpleNode node = vexNode.getTreenode();
			SimpleNode pNode = (SimpleNode) node.getFirstChildOfType(ASTDirectDeclarator.class);
			if(pNode != null && pNode.jjtGetNumChildren() > 0) {
				List<SimpleNode> list = pNode.findXpath(".//DirectDeclarator[@Leaf='true']");
				for(SimpleNode node2 :list) {
					if(node2.getImage().equals(varName)) {
						type = "����";
						break;
					}
				}
			}
			
		} else if (string.equals("1")) {
			SimpleNode treeNode = vexNode.getTreenode();
			List list = treeNode.findChildrenOfType(ASTUnaryExpression.class);
			if(list.size() > 1) {
				type = "ʹ�õ�";
			}
			
		} else if (string.equals("2")) {
			SimpleNode simpleNode = vexNode.getTreenode();
			ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) simpleNode
					.getFirstChildOfType(ASTInitDeclarator.class);
			// �޳�ʼ��
			if (astInitDeclarator.jjtGetNumChildren() == 1) {

			}
			// �г�ʼ��
			else if (astInitDeclarator.jjtGetNumChildren() == 2) {
				if (index > 1) {
					type = "ʹ�õ�";
				} else {
					SimpleNode node = (SimpleNode) simpleNode.getFirstChildOfType(ASTDirectDeclarator.class);
					if (varName.contains(node.getImage())) {
						type = "�����";
					}
					else {
						type = "ʹ�õ�";
					}
				}
			}
		} else if (string.equals("4")) {
			if (isVarNameAtLeft(vexNode, varName, index)) {
				type = "�����";
			} else {
				type = "ʹ�õ�";
			}
		} else if (string.equals("5")) {

		} else if (string.equals("6")) {

		} else if (string.equals("7")) {
			// �����Լ����������ʹ�õ�
			type = "ʹ�õ�";
		} else if (string.equals("8")) {

		}
		else if(string.equals("9")) {
			type = "ʹ�õ�";
		}
		return type;
	}

	/**
	 * ����һ��
	 * 
	 * @param vexNode
	 * @param varName
	 * @param index
	 * @return
	 */
	public String getVarType(VexNode vexNode, String varName) {
		String type = "";
		String string = getVexNodeType(vexNode);
		if (string.contains("0")) {
			type = "����";
		} else if (string.contains("1")) {
			type = "ʹ�õ�";
		} else if (string.contains("2")) {
			SimpleNode simpleNode = vexNode.getTreenode();
			ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) simpleNode
					.getFirstChildOfType(ASTInitDeclarator.class);
			// �޳�ʼ��
			if (astInitDeclarator.jjtGetNumChildren() == 1) {

			}
			// �г�ʼ��
			else if (astInitDeclarator.jjtGetNumChildren() == 2) {

				SimpleNode node = (SimpleNode) simpleNode.getFirstChildOfType(ASTDirectDeclarator.class);
				if (varName.contains(node.getImage())) {
					type = "�����";
				}
				else {
					type = "ʹ�õ�";
				}

			}
		} else if (string.contains("4")) {
			if (isVarNameAtLeft(vexNode, varName, 1)) {
				type = "�����";
			} else {
				type = "ʹ�õ�";
			}
		} else if (string.contains("5")) {

		} else if (string.contains("6")) {

		} else if (string.contains("7")) {
			// �����Լ����������ʹ�õ�
			type = "ʹ�õ�";
		} else if (string.contains("8")) {

		}
		return type;
	}

	/*
	 * add by lsc 2019/1/22 �ֱ��Ŀ��ڵ㿪ʼ�Ŀ�����ͼ�ϵ����пɴ�·����ÿ���ɴ�·���ϵĽڵ�������ݽ��������ڿ�����ͼ��Χ�ڽ�����Դ
	 * list�洢��Ҫ�����ı���������
	 */
	public void analysis_paths_flowNodes(List<String> path, String funcName, List<String> list) {
		// �ȷ���һ��·��
		String pathString = path.get(0);
		String[] strings = pathString.split("<-");
		Map<String, VexNode> map = getMapOfVexNode(funcName);

		// ��ʼ��
		list.add(args[3]);
		Set<Integer>set = new HashSet<>();
		set.add(Integer.parseInt(args[4]));
		map2.put(funcName, new HashSet<>(set));

		for (int i = 0; i < strings.length; i++) {
			VexNode vexNode = map.get(strings[i]);
			if (getVexNodeType(vexNode).contains("0")) {
				SimpleNode node = vexNode.getTreenode();
				ASTDirectDeclarator astDirectDeclarator = (ASTDirectDeclarator) node
						.getFirstChildOfType(ASTDirectDeclarator.class);

				// û�в���
				if (astDirectDeclarator.isLeaf()) {

				}
				// �в���
				else {
					List<SimpleNode> listNodes = astDirectDeclarator.findXpath(".//DirectDeclarator");
				}
			}
			// �����������ȫ�ֱ�������ʱ��������
			else if (getVexNodeType(vexNode).contains("1")) {
				continue;
			}
			// �ж������������
			else if (getVexNodeType(vexNode).contains("2")) {
				SimpleNode treeNode = vexNode.getTreenode();
				List<SimpleNode> listNodes = new ArrayList<>();
				listNodes.addAll(treeNode.findXpath(".//DirectDeclarator"));
				listNodes.addAll(treeNode.findXpath(".//PostfixExpression"));
			}
			// �޶������������
			else if (getVexNodeType(vexNode).contains("3")) {
				SimpleNode treeNode = vexNode.getTreenode();
				List<SimpleNode> listNodes = treeNode.findXpath(".//PostfixExpression");
			} else if (getVexNodeType(vexNode).contains("4")) {
				continue;
			}
			// �����ⲿ����Դ�⺯����������ֹ
			else if (getVexNodeType(vexNode).contains("5")) {

			}
			// i ++ �����
			else if (getVexNodeType(vexNode).contains("6")) {
				SimpleNode treeNode = vexNode.getTreenode();
				List<SimpleNode> listNodes = treeNode.findXpath(".//PostfixExpression");
			}
		}
	}

//	/**
//	 * �����﷨���ڵ㣬���Ǳ��ʽ(���еȺ�),��ȡ�ұߵı�������
//	 */
//	public List getRightNodes(SimpleNode node) {
//		VexNode vexNode = node.getCurrentVexNode();
//		List list = new ArrayList<>();
//		SimpleNode assignmentNode = (SimpleNode) node.getFirstChildOfType(ASTAssignmentExpression.class);
//		// �ж��������ڵ�(�и�ֵ���)
//		if (getVexNodeType(vexNode).contains("2.1")) {
//			list = assignmentNode.findChildrenOfType(ASTPostfixExpression.class);
//		}
//		// �ж��������������޸�ֵ���
//		else if (getVexNodeType(vexNode).contains("2.2")) {
//
//		}
//		// �޶��������ڵ�
//		else if (getVexNodeType(vexNode).contains("3")) {
//			if (assignmentNode != null && assignmentNode instanceof ASTAssignmentExpression
//					&& assignmentNode.jjtGetNumChildren() == 3) {
//
//				ASTAssignmentExpression rightExpr = (ASTAssignmentExpression) assignmentNode.jjtGetChild(2);
//
//				// ȡ���Ҳ���ʽ�����еı������б�
//				list = rightExpr.findChildrenOfType(ASTPostfixExpression.class);
//			}
//		}
//		return list;
//	}

	/**
	 * add by lsc
	 * �ж�һ���������ڵ��﷨���������ڵ��Ӧ��PostfixExpression(Ҳ������DirectDeclarator)�Ƿ���"="���
	 */
	public boolean isOnleftHandSide(SimpleNode node) {
		VexNode vexNode = node.getCurrentVexNode();
		// �ж��������ڵ�(�и�ֵ���)
		if (node instanceof ASTDirectDeclarator) {
			return true;
		}

		// �޶��������ڵ�
		else if (getVexNodeType(vexNode).contains("3")) {
			if (node instanceof ASTPostfixExpression) {
				SimpleNode assignmentNode = (SimpleNode) node.getFirstParentOfType(ASTAssignmentExpression.class);
				if (assignmentNode instanceof ASTAssignmentExpression && assignmentNode.jjtGetNumChildren() == 3) {
					return true;
				}
			}
		}

		return false;
	}

	/**
	 * ���� �������� �������� �кţ� ��ȡ���Ӧ��PostfixExpression(Ҳ������DirectDeclarator)�﷨���ڵ�
	 */
	public SimpleNode getSimpleNode(String funcName, String varName, int line) {
		VexNode vexNode = getVexNodeOflocate(funcName, varName, line);
		SimpleNode node = vexNode.getTreenode();
		List list = new ArrayList<>();
		if (!node.findXpath(".//PostfixExpression").isEmpty()) {
			list.addAll(node.findXpath(".//PostfixExpression"));
		}
		if (!node.findXpath(".//DirectDeclarator").isEmpty()) {
			list.addAll(node.findXpath(".//DirectDeclarator"));
		}

		for (int i = 0; i < list.size(); i++) {
			SimpleNode simpleNode = (SimpleNode) list.get(i);
			if (simpleNode instanceof ASTPostfixExpression) {
				if (simpleNode.jjtGetNumChildren() == 1) {
					SimpleNode simpleNode2 = (SimpleNode) simpleNode.jjtGetChild(0);
					if (varName.equals(simpleNode2)) {
						return simpleNode;
					}
				} else if (simpleNode.jjtGetNumChildren() > 1) {
					List list2 = simpleNode.findXpath(".//PrimaryExpression");
					boolean flag = true;
					for (int j = 0; j < list2.size(); j++) {
						SimpleNode node2 = (SimpleNode) list2.get(i);
						if (!varName.contains(node2.getImage())) {
							flag = false;
							break;
						}
					}

					if (flag) {
						return simpleNode;
					}
				}
			} else if (simpleNode instanceof ASTDirectDeclarator) {
				if (simpleNode.getImage().equals(varName)) {
					return simpleNode;
				}
			}

		}
		return node;

	}

	/**
	 * add by lsc 2019/2/15 �жϱ����Ƿ��ڸ�ֵ���ʽ�����(�������) ����3�������ʽ���ڿ��������vexNode ,
	 * ������varName , ������������index
	 */
	public boolean isVarNameAtLeft(VexNode vexNode, String varName, int index) {

		String string = getVexNodeType(vexNode);
		if (index > 1) {
			return false;
		}
		// �ж����������
		if (string.contains("2")) {
			SimpleNode simpleNode = vexNode.getTreenode();
			ASTInitDeclarator astInitDeclarator = (ASTInitDeclarator) simpleNode
					.getFirstChildOfType(ASTInitDeclarator.class);
			// �޳�ʼ�����
			if (astInitDeclarator.jjtGetNumChildren() == 1) {
				return false;
			}
			// �г�ʼ�����
			else if (astInitDeclarator.jjtGetNumChildren() == 2) {
				ASTDirectDeclarator astDirectDeclarator = (ASTDirectDeclarator) astInitDeclarator
						.getFirstChildOfType(ASTDirectDeclarator.class);
				String str = astDirectDeclarator.getImage();
				if (str.equals(varName)) {
					return true;
				}
			}
		}
		// �޶����������
		else if (string.contains("4")) {
			SimpleNode simpleNode = vexNode.getTreenode();
			ASTUnaryExpression astUnaryExpression = (ASTUnaryExpression) simpleNode
					.getFirstChildOfType(ASTUnaryExpression.class);
			String varString = getVarNameFromUnaryNode(astUnaryExpression);
			if (varName.equals(varString)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * ����UnaryExpression�﷨���ڵ��ȡ��Ӧ�ı��������� add by lsc 2019/2/17
	 */
	public String getVarNameFromPostNode(SimpleNode node) {
		String varName = "";
		if (node instanceof ASTPostfixExpression) {
			if (node.jjtGetNumChildren() == 1) {
				SimpleNode node2 = (SimpleNode) node.getFirstChildOfType(ASTPrimaryExpression.class);
				varName = node2.getImage();
			} else {

				if (node.getOperators().contains(".") || node.getOperators().contains("->")) {
					SimpleNode node2 = (SimpleNode) node.getFirstChildOfType(ASTPrimaryExpression.class);
					varName = node2.getImage();
					List<SimpleNode> list = node.findDirectChildOfType(ASTFieldId.class);
					for (SimpleNode nSimpleNode : list) {
						String str = "." + nSimpleNode.getImage();
						varName += str;
					}
				} else if (node.getOperators().contains("(")) {
					SimpleNode node2 = (SimpleNode) node.getFirstChildOfType(ASTPrimaryExpression.class);
					varName = node2.getImage();
					SimpleNode nSimpleNode = (SimpleNode) node.getFirstChildInstanceofType(ASTPostfixExpression.class);
					if (nSimpleNode != null) {
						varName = varName + "(" + getVarNameFromPostNode(nSimpleNode);
					}

				}
			}
		}

		return varName;

	}
	
	public String getVarNameFromUnaryNode(SimpleNode node) {
		StringBuffer sBuffer = new StringBuffer();
		//ֱ��������image
		if(node instanceof ASTDirectDeclarator) {
			ASTDirectDeclarator declarator = (ASTDirectDeclarator) node;
			sBuffer.append(declarator.getImage());
		
		}else if(node instanceof ASTUnaryExpression) {
			//��ʼ�����ӱ���
			List<SimpleNode> simple = node.findDirectChildOfType(ASTPostfixExpression.class);
			if(!simple.isEmpty()&&simple.size()==1) {
				ASTPostfixExpression postfixExpression = (ASTPostfixExpression) simple.get(0);
				if (postfixExpression.jjtGetNumChildren() == 1) {
					SimpleNode node2 = (SimpleNode) postfixExpression.getFirstChildOfType(ASTPrimaryExpression.class);
					sBuffer.append(node2.getImage());
				} else {
					if (postfixExpression.getOperators().contains(".") ) {
						SimpleNode node2 = (SimpleNode) postfixExpression.getFirstChildOfType(ASTPrimaryExpression.class);
						sBuffer.append(node2.getImage());
						List<SimpleNode> list = postfixExpression.findDirectChildOfType(ASTFieldId.class);
						for (SimpleNode nSimpleNode : list) {
							sBuffer.append(".").append(nSimpleNode.getImage());
						}
					} else if(postfixExpression.getOperators().contains("->")) {
						SimpleNode node2 = (SimpleNode) postfixExpression.getFirstChildOfType(ASTPrimaryExpression.class);
						sBuffer.append(node2.getImage());
						List<SimpleNode> list = postfixExpression.findDirectChildOfType(ASTFieldId.class);
						for (SimpleNode nSimpleNode : list) {
							sBuffer.append("->").append(nSimpleNode.getImage());
						}
					}else if (postfixExpression.getOperators().contains("(")) {
						SimpleNode node2 = (SimpleNode) postfixExpression.getFirstChildOfType(ASTPrimaryExpression.class);
						sBuffer.append(node2.getImage());
						SimpleNode nSimpleNode = (SimpleNode) postfixExpression.getFirstChildInstanceofType(ASTPostfixExpression.class);
						if (nSimpleNode != null) {
							sBuffer.append("(").append(getVarNameFromUnaryNode(nSimpleNode));
						}
					}else if(postfixExpression.getOperators().contains("[")) {
						SimpleNode node2 = (SimpleNode) postfixExpression.getFirstChildOfType(ASTPrimaryExpression.class);
						sBuffer.append(node2.getImage());
						List<SimpleNode> list = postfixExpression.findDirectChildOfType(ASTExpression.class);
						for (SimpleNode nSimpleNode : list) {
							SimpleNode node3 = (SimpleNode) postfixExpression.getFirstChildOfType(ASTPrimaryExpression.class);
							if(node3.jjtGetNumChildren()==0) {
								sBuffer.append("[").append(node3.getImage()).append("]");
							}else if(node3.jjtGetNumChildren()==1){
								SimpleNode node4 = (SimpleNode) postfixExpression.getFirstChildOfType(ASTConstant.class);
								sBuffer.append("[").append(node4.getImage()).append("]");
							}else {
								sBuffer.append("[]");
							}
						}
					}
					
				}
			}else if(simple.isEmpty()){
				List<SimpleNode> ASTUnaryOperator =  node.findDirectChildOfType(ASTUnaryOperator.class);
				if(ASTUnaryOperator.size()>0) {
					ASTUnaryOperator unaryOperator = (softtest.ast.c.ASTUnaryOperator) ASTUnaryOperator.get(0);
					if(unaryOperator.getOperators().equals("*")||unaryOperator.getOperators().equals("&")) {
						ASTPrimaryExpression node5 = (ASTPrimaryExpression) node.getFirstChildInstanceofType(ASTPrimaryExpression.class);
						sBuffer.append(node5.getImage());
					}
				}
			}else {
				System.err.println("unary�ڵ����ж��ASTPostfixExpression");
			}
		}
		return sBuffer.toString();
	}
	
	
	
	

	/**
	 * add by lsc 2019/2/27 ��ֵ��Ϣʶ�� �ж�ʹ�õ��Ӧ������(����Ϊ����������������)
	 * ����Ϊʹ�õ��Ӧ��UnaryExpression�ڵ�
	 */
	public boolean isDefFinish(SimpleNode node) {
		if (node instanceof ASTUnaryExpression) {
			ASTPostfixExpression astPostfixExpression = (ASTPostfixExpression) node
					.getFirstChildOfType(ASTPostfixExpression.class);
			List list = astPostfixExpression.findXpath(".//PrimaryExpression[@Method='true']");
			if (list.size() != 0) {
				// ��Ϊ�Զ���ĺ���
				if (list_function.contains(list.get(0))) {
					return false;
				} else {
					return true;
				}
			} else {
				ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression) node
						.getFirstChildOfType(ASTPrimaryExpression.class);
				// ��Ϊ����
				if (astPrimaryExpression.isLeaf()) {
					return false;
				} else {
					return true;
				}
			}
		}
		return false;
	}

	/**
     * �ݹ鴦����
     * add by lsc 2019/3/11
     * @param vexNode Ŀ�����ڿ������ڵ�
     * @param funcName ������
     * @param varName ������
     * @param index �����жϱ������͵�����
     */
    private void dfs(VexNode vexNode ,String funcName, String varName ,int index) {
    	if(map2.containsKey(funcName)) {
    		map2.get(funcName).add(vexNode.getTreenode().getBeginLine());
    	}
    	else {
    		HashSet<Integer> set = new HashSet<>();
    		set.add(vexNode.getTreenode().getBeginLine());
    		map2.put(funcName, set);
    	}
    	
    	//add by lsc �����ź���׷�����
    	String str = varName+":"+vexNode.getTreenode().getBeginLine()+":"+getVarType(vexNode, varName, index);
    	if(! Semaphore_tracking.contains(str)) {
    		Semaphore_tracking.add(str);
    	}
		
    	
    	if(getVarType(vexNode, varName, index).equals("�����") ) {
    		
    		System.out.println(varName + " : " + getVarType(vexNode, varName, index) + vexNode.getTreenode().getBeginLine());
    		
    		
    		
    		List<SimpleNode> uSimpleNodes = getASTUnaryExpression(vexNode);
    		int count = 0;
    		for(SimpleNode simpleNode : uSimpleNodes) {
    			if(count == 0) {
    				count ++;
    				continue;
    			}
    			//��������
    			varName = getVariableInfo(simpleNode);
    			if(isNumber(simpleNode)){
    				//�ս��
                    System.out.println("�ս��"+varName);    				
    			}else if(isSimpleVariable(simpleNode)){
    				//�򵥱��� a��ab
    				dfs(vexNode,funcName,varName,2);
    				System.out.println("�򵥱���"+varName); 
    			}else if(isComplexVariable(simpleNode)){
    				//���ӱ��� a.b, a->b
    				dfs(vexNode,funcName,varName,2);
    				System.out.println("���ӱ���"+varName); 
    			}else if(isArrayVariable(simpleNode)){
    				//���� a[1]
    				dfs(vexNode,funcName,varName,2);
    				System.out.println("����"+varName);
    			}else if(isFunction(simpleNode)){
    				//��������
    				String functionName[] = varName.split("\\(");
    				varName = functionName[0];
    				SimpleNode funNode = map_function_simpleNode.get(varName);
    					
    				try {
    					ArrayList<SimpleNode> returnNode = (ArrayList<SimpleNode>) funNode.findXpath(".//JumpStatement");
        				//������ú�������ֵ���֣��ֽⷵ��ֵ�ı��ʽ
        				for(int j = 0; j<returnNode.size();j++){
        					SimpleNode tem = returnNode.get(j);
        					if(tem.getImage().equals("return")){
        						List<SimpleNode> returnList =  getASTUnaryExpression(tem.getCurrentVexNode());
        		                sloveRetrunFunction(returnList,tem.getCurrentVexNode(),varName);
        					}
        				}
        				System.out.println("����"+varName);
    				}catch (Exception e) {
						// TODO: handle exception
					}
    			
    			}
    		}
        		
    	}
    	else if(getVarType(vexNode, varName, index).equals("ʹ�õ�")) {
    		List<SimpleNode> nodes = getASTUnaryExpression(vexNode);
    		List<List<VexNode>> listtemp = new ArrayList<>();
    		List<List<VexNode>> curPaths = findpathNew(new ArrayList<VexNode>(), vexNode, listtemp);
    		for(List <VexNode> tem_nodes: curPaths) {
    			for(VexNode vex : tem_nodes) {
    				if(vexNode.getName()==vex.getName()) {
    					continue;
    				}
    				
    				//add by lsc 2019/4/2 ���ӶԿ�������Դ��Լ����Ϣ�Ĵ���
    				if(vex.toString().contains("if_head") || vex.toString().contains("while_head") || vex.toString().contains("switch_head")) {
    					SimpleNode treeNode = vex.getTreenode();
    					SimpleNode node = (SimpleNode) treeNode.getFirstChildOfType(ASTAssignmentExpression.class);
    					SimpleNode pNode = (SimpleNode) node.getFirstDirectChildOfType(ASTLogicalANDExpression.class);
    					if(pNode == null) {
    						SimpleNode newNode = (SimpleNode) node.getFirstChildOfType(ASTUnaryExpression.class);
    						String newVarName = getVarNameFromUnaryNode(newNode);
    						dfs(vex, funcName, newVarName, 1);
    						if(! controList.contains(newVarName+":"+vex.getTreenode().getBeginLine())) {
    							controList.add(newVarName+":"+vex.getTreenode().getBeginLine());
    						}
    						
    					}
    					else {
    						for(int i = 0 ; i < pNode.jjtGetNumChildren() ; i ++) {
    							SimpleNode newNode = (SimpleNode) ((SimpleNode)pNode.jjtGetChild(i)).getFirstChildOfType(ASTUnaryExpression.class);
        						String newVarName = getVarNameFromUnaryNode(newNode);
        						dfs(vex, funcName, newVarName, 1);
        						if(! controList.contains(newVarName+":"+vex.getTreenode().getBeginLine())) {
        							controList.add(newVarName+":"+vex.getTreenode().getBeginLine());
        						}
    						}
    					}
    				}
    			}
    		}
    		//�½���ʼ ywj
    		
    		//�򵥱���
    		if(isSimpleName(varName)) {
    			boolean isGlobal = true;
    			 for(List<VexNode> path : curPaths) {
 	    	    	for(VexNode vex : path) {
 	    				if(vexNode==vex ) {
 	    					continue;
 	    				}
 	    				if(getVarType(vex,varName,1).contains("�����")) {
 	    					 List<SimpleNode> returnList = getASTUnaryExpression(vex);
 	    					 SimpleNode simp = returnList.get(0);
 	    					 if(varName.equals(getVarNameFromUnaryNode(simp))) {
 	    						 isGlobal = false;
 	 	   						 dfs(vex,funcName,varName,1);
 	 	   						 break;
 	    					 }
 	   					 }
 	    				if(getVarType(vex,varName,1).equals("����")) {
 	    					 isGlobal = false;
 	    					 dfs(vex,funcName,varName,1);
 	    					 break;
 	    				}
 	    	    	}
 	    	    }
    			if(isGlobal) {
    				 JoinGlobalOutFunc(varName);
    			}
    		}else {
	    		//�����ӱ���
	    		boolean isfound =false;
	    	    for(List<VexNode> path : curPaths) {
	    	    	for(VexNode vex : path) {
	    				if(vexNode==vex ) {
	    					continue;
	    				}
	    				if(getVexNodeType(vex).contains("4")) {
		   					List<SimpleNode> list  = getASTUnaryExpression(vex);
		   					ASTUnaryExpression astUnaryExpression = (ASTUnaryExpression) list.get(0);
		   					String string = getVarNameFromUnaryNode(astUnaryExpression);
		   					//�ҵ����ӱ���
		   					 if(string.equals(varName)) {
		   						 isfound=true;
		   						 dfs(vex,funcName,varName,1);
		   						 break;
		   					 }
	    				}
	    	    	}
	    	    }
	    	    //û���ҵ����ӱ���
	    		if(!isfound) {
	    			//����ѵ�ǰ·�����Ҳ����ļ򵥱���ȫ���ռ��������ж��ǲ���ȫ�ֱ���
	    			List<String> var = isGetGlobal(vexNode,funcName,varName,curPaths);
	    			for(String string : var) {
	    				if(isGlobal(string)) {
	    					boolean f2=false;
	    					  for(List<VexNode> path : curPaths) {
	    						    boolean f1=false;
	    			    	    	for(VexNode vex : path) {
	    			    	    		if(vexNode==vex ) {
	    			    					continue;
	    			    				}
	    			    	    		List<SimpleNode> list = vex.getTreenode().findXpath(".//PrimaryExpression[@Method='true']");
	    			    	    		if(list.isEmpty()) {
	    			    	    			continue;
	    			    	    		}else {
	    			    	    			for(SimpleNode simpleNode:list) {
	    			    	    				ASTPrimaryExpression primaryExpression = (ASTPrimaryExpression) simpleNode;
	    			    	    				if(global_func.containsKey(primaryExpression.getImage())) {
	    			    	    					List<Map<VexNode, String>> ls = global_func.get(primaryExpression.getImage());
	    			    	    					for(int j=0;j<ls.size();j++) {
	    			    	    						Map<VexNode, String> map = ls.get(j);
	    			    	    						for(VexNode vex_global :map.keySet()) {
	    			    	    							if(map.get(vex_global).equals(string)) {
		    			    	    							dfs(vex_global,primaryExpression.getImage() , string, 1);
		    			    	    							f1=true;
		    			    	    							f2=true;
		    			    	    						}
	    			    	    						}
	    			    	    						if(f1) {
	    			    	    							break;
	    			    	    						}
	    			    	    					}
	    			    	    				}
	    			    	    				if(f1) {
			    	    							break;
			    	    						}
	    			    	    			}
	    			    	    		}
	    			    	    		if(f1) {
	    			    	    			break;
	    			    	    		}
	    			    	    	}
	    					  }
	    					  if(!f2) {
	    						  JoinGlobalOutFunc(string);
	    					  }
	    				}else {
	    					System.out.println("�Ҳ���ȫ�ֱ�����"+string);
	    				}
	    				
	    			}
	    			
	    		}
    		}
    		//�¼ӽ��� ywj
//    		for(List <VexNode> tem_nodes: curPaths) {
//    			for(VexNode vex : tem_nodes) {
//    				if(vexNode.getName()==vex.getName()) {
//    					continue;
//    				}
//    				
//    				
//    				if(getVarType(vex,varName,1).contains("�����") || getVarType(vex, varName , 1).equals("����")){
//    					List<SimpleNode> curNodes = getASTUnaryExpression(vex);
//        				if(curNodes.size() > 0) {
//        					SimpleNode node = curNodes.get(0);
//        					if(getVarNameFromUnaryNode(node).equals(varName)) {
//        						dfs(vex, funcName, varName, 1);
//        						break;
//        					}
//        				}
//    				}
//    			}
//    		}
//    		for(List <VexNode> tem_nodes: curPaths) {	
//    			for(VexNode vex : tem_nodes) {
//    				if(vexNode.getName()==vex.getName()) {
//    					continue;
//    				}
//    				
//    				
//    				if(getVarType(vex,varName,1).contains("�����") || getVarType(vex, varName , 1).equals("����")){
//    			
//    					
//    					dfs(vex,funcName,varName,1);
//    					break;
//    				}
//    			}
//    		}
    		
    	}
    	else if(getVarType(vexNode, varName, index).equals("����")) {

    		System.out.println("��ǰ������ �� "+ varName + "   �к���  �� "+vexNode.getTreenode().getBeginLine());
    		System.out.println("vexNode : " + vexNode + "   "+vexNode.getTreenode().getImage());
    		
    		
    		//��÷����������﷨���ڵ�,(֮����Լ�ӻ�ȡ�������������Ϣ)
			ASTFunctionDefinition funcdef = (ASTFunctionDefinition) vexNode.getTreenode();
			

			System.err.println("funcdef ��Ӧ������: " + funcdef.getImage());
			
			//����˲�����������ȷ�����⣬ԭ������������ȡ��ʽ��������(���ܱ�֤funcdef.getScope()�Ĳ��������µĴ������������﷨������֤��ȷ).
			String[] ParameterList = new String[funcdef.findXpath(".//ParameterDeclaration").size()];
			System.out.println(funcdef.getParameterCount());
			int count = 0;

				System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
				System.out.println(funcdef.getImage());

				List<SimpleNode> list = funcdef.findXpath(".//ParameterDeclaration");
				for(SimpleNode simpleNode : list) {
					List<SimpleNode>list2 = simpleNode.findXpath(".//Declarator");
					
					
					for(SimpleNode simpleNode2 : list2){
						System.out.println(simpleNode2.getImage()+":"+simpleNode2.getBeginLine());
						ParameterList[count ++] = simpleNode2.getImage();
					}
				}
				
		
				System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");

			
			

			int indexOfParameter = 0 ;

			
			System.out.println("��ǰ����  "+ varName);
			
			
			for(int i = 0 ; i < count ; i ++) {
				if(varName.equals(ParameterList[i])) {
					indexOfParameter = i + 1;
					break;
				}
			}
			
			
			System.out.println("�ó��˱�����"+varName+"��indexΪ:" + indexOfParameter);
			
			
			if(funcdef!=null) {
				
				String funNameString = funcdef.getImage();
				List<String> listfuncList = map_function.get(funNameString);
				System.out.println(funcdef + "  " + map_function.get(funNameString));
				System.out.println("test : ");
				
				if(listfuncList != null) {
					for(String string : listfuncList) {
						
						
						System.out.println(map_function_simpleNode.get(string));
						System.out.println("���������� " + string);
						SimpleNode astFunctionDeclaration =  map_function_simpleNode.get(string);
				
						
						List<SimpleNode> listnodeList = astFunctionDeclaration.findXpath(".//PrimaryExpression[@Method='true']");
						System.err.println(list_outsource);
						
						
						for(SimpleNode node : listnodeList) {
							//add by lsc 2019/4/1 �ų��⺯��
							if(list_outsource.contains(node.getImage())) {
								continue;
							}
							
							if(node.getImage().equals(funNameString)) {
								System.out.println("today : " + node.getImage() + node.getBeginLine());
								String fileName = map_function_path.get(string);
								funcName = string;
								ASTPostfixExpression astPostfixExpression = (ASTPostfixExpression) node.jjtGetParent();
								System.out.println("���ڵ���:" +astPostfixExpression);
								List<SimpleNode> nodes = astPostfixExpression.findXpath(".//PrimaryExpression[@Method='false']");
								
								
								System.out.println("indexOfParameter is  :" + indexOfParameter);
								
								if(indexOfParameter > 0) {
									String symbolName = nodes.get(indexOfParameter - 1).getImage();
									int line1 = node.getBeginLine();
									
									vexNode = nodes.get(indexOfParameter - 1).getCurrentVexNode();
									varName = symbolName;
									System.err.println(map_function_simpleNode.get(funcName).getImage()+"   "+funcName + "  "+ symbolName + "    " + vexNode.getTreenode().getBeginLine() + getVarType(vexNode, varName, 1));
									
								    
									
									dfs(vexNode, funcName, varName, 2);
								}
						
							}
						}
						
						
						
					}
				}
		
				

			}
		}
    	
    	
    	
    	//������Ŀ�������ͣ�����㣬ʹ�õ㣬����
    	
    	//Ȼ��������Ӧ���ͽ��зֱ�Ĵ���
    	
    	/**
    	 * 1	.����������� ��ֵ�������ж����Ƿ�Ϊ�ս�������Ⱥ��ұ߾�Ϊ�ս����ֹͣ������ݹ����ұ߷��ս����������Ŀ���
    	 * 2	ʹ�õ������ ����·������ÿ���ڵ�Ķ���㣬�������ֵ���ڵ�ǰ��Ŀ���)�����֣��ã�����Ŀ���
    	 * 3. 	����ʹ�������
    	 */
    	
    	
    	
//    	String typeString = getVarType(vexNode, varName, index)
    	
    }
    
    
    /**
     * add by ywj 2019/3/13
     */
    public List<SimpleNode> getASTUnaryExpression(VexNode vex ){
    	SimpleNode node = vex.getTreenode();
    	List<SimpleNode> list = new ArrayList<SimpleNode>();
    	List<SimpleNode> list_U = new ArrayList<SimpleNode>();
    	if(! node.findXpath(".//UnaryExpression").isEmpty()) {
			list_U.addAll(node.findXpath(".//UnaryExpression"));
		}
		if(! node.findXpath(".//DirectDeclarator").isEmpty()) {
			list.addAll(node.findXpath(".//DirectDeclarator"));
		}
		List<SimpleNode> list_U1 = new ArrayList<SimpleNode>();
		for(SimpleNode temp_node : list_U) {
			if(temp_node.getParentsOfType(ASTUnaryExpression.class).isEmpty()) {
				list_U1.add(temp_node);
			}
		}
		list.addAll(list_U1);
	  	return list;
    }
    
    /**
     * add by lsc 2019/3/13
     * ���ݺ��������䷵��ֵ�ڵ㴦���еķ��ر������������ֵ�а����к���(���뵱ǰ������������ԣ�Ϊ�˷�ֹ��ѭ��)���������
     */
    
    
    
    
    
    /**
     * ��ȡ�⺯��
     * @param 
     * @return
     */
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
    
    

    private boolean isNumber(SimpleNode node){
    	
    	ArrayList<SimpleNode> list = (ArrayList<SimpleNode>) node.findXpath(".//Constant");
    	if(node.findXpath(".//Constant")!=null&&node.findXpath(".//Constant").size()!=0){
    		if(((SimpleNode)node.jjtGetChild(0)).getOperators().equals("")){
    			return true;
    		}else{
    			return false;
    		}	
    	}else{
    		return false;
    	}
    	
    }
    
    
    private boolean isSimpleVariable(SimpleNode node){
    	node = (SimpleNode)node.jjtGetChild(0);
    	for(int i = 0; i<node.jjtGetNumChildren();i++){
    		if(node.jjtGetChild(i) instanceof ASTPrimaryExpression){
    			continue;
    		}
    		return false;
    	}    	
    	if(node.getOperators().equals("")){
			return true;
		}else{
			return false;
		}
    }
    
    private boolean isComplexVariable(SimpleNode node){
    	if(( node.findXpath(".//PostfixExpression/PrimaryExpression").size()==1 )&&( node.findXpath(".//PostfixExpression/FieldId").size()>=1)){
    		return true;
    	}else{
    		return false;
    	}
    }
    
    private boolean isArrayVariable(SimpleNode node){
    	node = (SimpleNode)node.jjtGetChild(0);
    	int priNum = 0;
    	int exprNum = 0;
    	for(int i = 0; i<node.jjtGetNumChildren();i++){
    		if(node.jjtGetChild(i) instanceof ASTPrimaryExpression){
    			priNum++;;
    		}else if(node.jjtGetChild(i) instanceof ASTExpression){
    			exprNum++;
    		}else {
    			return false;
    		}
    	}
    	
    	if(priNum == 1 && exprNum >=1){
    		return true;
    	}else{
    		return false;
    	}
    	
    }
    
    private boolean isFunction(SimpleNode node){
    	
    	node = (SimpleNode) node.jjtGetChild(0);
    	int priNum = 0;
    	int argNum = 0;
    	for(int i = 0;i<node.jjtGetNumChildren();i++){
    		if(node.jjtGetChild(i)instanceof ASTPrimaryExpression){
    			priNum ++;
    		}else if(node.jjtGetChild(i) instanceof ASTArgumentExpressionList){
    			argNum++;
    		}
    	}
    	
    	if(priNum == 1 &&argNum==1){
    		return true;
    	}else if(priNum == 1&&node.getOperators().equals("(")){
    		return true;
    	}else{
    		return false;
    	}
    	
    }
    
    private String getVariableInfo(SimpleNode nodes){
    	
    	String result = "";
    	for(int i = 0;i<nodes.jjtGetNumChildren();i++ ){
    		SimpleNode node = (SimpleNode) nodes.jjtGetChild(i);
    		int index = 0;
    		String operaters[] = node.getOperators().split(" ");
    		for(int j = 0; j< node.jjtGetNumChildren();j++){
    			
    			if(node.jjtGetChild(j) instanceof ASTPrimaryExpression){
    				result += ((SimpleNode)node.jjtGetChild(j)).getImage();
    			}else if(node.jjtGetChild(j) instanceof ASTArgumentExpressionList){
    				//����
    				result += "()";
    			}else if(node.jjtGetChild(j) instanceof ASTFieldId){
    				//���ӽṹ��,��Ҫָָ������
    				result += operaters[index]+((SimpleNode)(node.jjtGetChild(j))).getImage();
    				index++;
    			}else if(node.jjtGetChild(j)instanceof ASTExpression){
    				//�������
    				ArrayList<SimpleNode> nodeList =  (ArrayList<SimpleNode>) ((SimpleNode)node.jjtGetChild(j)).findXpath(".//PrimaryExpression[@Method='false']");
    				
    				for(SimpleNode temNode:nodeList){
    					if(!temNode.getImage().equals("")){
    						result = result + "["+temNode.getImage()+"]";
    					}else{
    						result = result + "[" + ((SimpleNode)(temNode.findXpath(".//Constant").get(0))).getImage()+"]";
    					}
    					
    				}
    			}else{
    				System.out.println("���ͽ�����������");
    			}
    		}
    		if(operaters.length!=0&&operaters[0].equals("(")){
    			result+="()";
    		}
    	}
    	
    	if(result.equals("")){
    		ArrayList<SimpleNode> endResult =  (ArrayList<SimpleNode>)nodes.findXpath(".//PostfixExpression/PrimaryExpression/Constant");
    		for(SimpleNode end:endResult){
    			result += end.getImage();
    		}
		}
    	
    	
    	
    	return result;
    }
    
    
    private void sloveRetrunFunction(List<SimpleNode>returnList,VexNode vexNode,String funcName){
    	for(int i = 0;i<returnList.size();i++){
			SimpleNode node = returnList.get(i);
			String typeString = getVariableInfo(node);
			if(isNumber(node)){
				//�ս��
				System.out.println("�ս��");
			}else if(isSimpleVariable(node)){
				dfs(vexNode,funcName,typeString,2);
				System.out.println("�򵥱���"+typeString);
			}else if(isComplexVariable(node)){
				dfs(vexNode,funcName,typeString,2);
				System.out.println("���ӱ���"+typeString);
			}else if(isArrayVariable(node)){
				dfs(vexNode,funcName,typeString,2);
				System.out.println("����"+typeString);
			}else if(isFunction(node)){
				//��������
				String functionName[] = typeString.split("\\(");
				typeString = functionName[0];
				SimpleNode funNode = map_function_simpleNode.get(typeString);
				ArrayList<SimpleNode> returnNode = (ArrayList<SimpleNode>) funNode.findXpath(".//JumpStatement");
				//������ú�������ֵ���֣��ֽⷵ��ֵ�ı��ʽ
				for(int j = 0; j<returnNode.size();j++){
					SimpleNode tem = returnNode.get(j);
					if(tem.getImage().equals("return")){
						List<SimpleNode> list =  getASTUnaryExpression(tem.getCurrentVexNode());
		                sloveRetrunFunction(list,tem.getCurrentVexNode(),typeString);
					}
				}
				System.out.println("����"+typeString);
			}
		}
    }
    
    //�¼� ywj
    private  List<String> spiltVarname(String varName) {
		List<String> list = new ArrayList<>();
		//�ṹ��
		if(varName.contains(".")) {
			int Lastindex = varName.lastIndexOf(".");
			String string = varName.substring(0, Lastindex);
			list.add(string);
		}else if(varName.contains("->")) {
			int Lastindex = varName.lastIndexOf("->");
			String string = varName.substring(0, Lastindex);
			list.add(string);
		//����
		}else if(varName.contains("[")) {
			varName = varName.replaceAll("]","");
			varName = varName.replaceAll("\\[",",");
			String[] st = varName.split(",");
			for(String temp:st) {
				if(!isNumeric(temp)) {
					list.add(temp);
				}
			}
		}else if(varName.contains("*")){
			int Lastindex = varName.lastIndexOf("*");
			String string = varName.substring(Lastindex+1);
			list.add(string);
		}else if(varName.contains("&")) {
			int Lastindex = varName.lastIndexOf("&");
			String string = varName.substring(Lastindex+1);
			list.add(string);
		}
		return list;
	}
	private boolean isNumeric(String str){
		for (int i = 0; i < str.length(); i++){
			if (!Character.isDigit(str.charAt(i))){
				return false;
				}
			}
		return true;
	}
	private boolean isSimpleName(String varName) {
		//����ָ�������ַ�������򵥱�������
		if(varName.contains("[")||varName.contains(".")||varName.contains("->")) {
			return false;
		}
		return true;
	}
	private List<String> isGetGlobal(VexNode vexNode ,String funcName, String varName ,List<List<VexNode>> curPaths){
		List<String> list = new ArrayList<>();
		if(isSimpleName(varName)) {
			if(!dfsUsed(vexNode,funcName,varName,curPaths)) {
				list.add(varName);
			}
		}else {
			List<String> var = spiltVarname(varName);
			for(int i=0;i<var.size();i++) {
				String var_temp = var.get(i);
				if(dfsUsed(vexNode,funcName,var_temp,curPaths)) {
					continue;
				}else {
					if(isSimpleName(var_temp)) {
						list.add(var_temp);
					}else {
						for(String st : isGetGlobal(vexNode,funcName,var_temp,curPaths)) {
							list.add(st);
						}
					}
				}
			}
		}
		return list;
	}
	/**
	 * 
	 * @param vexNode
	 * @param funcName
	 * @param varName
	 * @param index
	 */
	private boolean dfsUsed(VexNode vexNode ,String funcName, String varName ,List<List<VexNode>> curPaths ) {
		boolean isfound=false;
		boolean isGlobal=true;
		if(isSimpleName(varName)) {
			for(List<VexNode> path : curPaths) {
	    	    	for(VexNode vex : path) {
	    				if(vexNode==vex ) {
	    					continue;
	    				}
	    				if(getVarType(vex,varName,1).contains("�����")) {
	    					 List<SimpleNode> returnList = getASTUnaryExpression(vex);
	    					 SimpleNode simp = returnList.get(0);
	    					 if(varName.equals(getVarNameFromUnaryNode(simp))) {
	    						 isGlobal = false;
	 	   						 dfs(vex,funcName,varName,1);
	 	   						 break;
	    					 }
	   					 }
	    				if(getVarType(vex,varName,1).equals("����")) {
	    					 isGlobal = false;
	    					 dfs(vex,funcName,varName,1);
	    					 break;
	    				}
	    	    	}
	    	    }
//			if(isGlobal) {
//				return true;
//			}
		}else {
			for(List<VexNode> path : curPaths) {
    	    	for(VexNode vex : path) {
    				if(vexNode==vex ) {
    					continue;
    				}
    				if(getVarType(vex,varName,1).contains("�����")) {
	   					List<SimpleNode> list  = getASTUnaryExpression(vex);
	   					ASTUnaryExpression astUnaryExpression = (ASTUnaryExpression) list.get(0);
	   					String string = getVarNameFromUnaryNode(astUnaryExpression);
	   					//�ҵ����ӱ���
	   					 if(string.equals(varName)) {
	   						 isfound=true;
	   						 dfs(vex,funcName,varName,1);
	   						 break;
	   					 }
    				}
    	    	}
    	    }
		}
		return isfound||!isGlobal;
	}
	/**
	 * ���ݱ�����
	 * @param varName
	 * @return
	 */
	public boolean isGlobal(String varName) {
		boolean flag = false;
		for(List<String> st1: global_VariablesList) {
			if(st1.isEmpty()) {
				continue;
			}else {
				if(varName.equals(st1.get(1))) {
					flag=true;
					break;
				}
			}
		}
		return flag;
	}
	public void JoinGlobalOutFunc(String varName) {
		for(List<String> st1: global_VariablesList) {
			if(st1.isEmpty()) {
				continue;
			}else {
				if(varName.equals(st1.get(1))) {
					if(map2.containsKey(st1.get(0))) {
			    		map2.get(st1.get(0)).add(Integer.parseInt(st1.get(2)));
			    	}
			    	else {
			     		HashSet<Integer> set = new HashSet<>();
			    		set.add(Integer.parseInt(st1.get(2)));
			    		map2.put(st1.get(0), set);
			    	}
					break;
				}
			}
		}
	}
}
