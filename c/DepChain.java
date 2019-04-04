package softtest.depchain.c;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import com.alibaba.fastjson.JSON;
import com.alibaba.fastjson.JSONArray;
import com.alibaba.fastjson.JSONObject;
import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTFunctionDeclaration;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
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
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.interpro.c.Method;
import softtest.interpro.c.MethodNode;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.rules.gcc.fault.OOB_CheckStateMachine;
import softtest.scvp.c.Position;
import softtest.scvp.c.SCVPString;
import softtest.scvp.c.SCVPVisitor;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;


public class DepChain {
	private List<AnalysisElement> elements= new ArrayList<AnalysisElement>();;
	private String analysisDir="";
	private List<String> files=new ArrayList<String>();			//用于存储收集到的所有.c文件
	private InterCallGraph interCGraph =InterCallGraph.getInstance();
	private String[] args;
	private Pretreatment pre=new Pretreatment();
	
	public DepChain(String[] args)
	{
		this.analysisDir=args[1];
		this.setArgs(args);
		init();
	}
	private HashMap<String, ASTTranslationUnit> astmap = new HashMap<String, ASTTranslationUnit>();
	private HashMap<String, Graph> cfgmap = new HashMap<String, Graph>();
	private HashMap<Graph, String> cfgmap2 = new HashMap<Graph, String>();
	private HashMap<String, CGraph> cgMap = new HashMap<String, CGraph>();
	//收集测试路径下的所有.C源文件
	private void collect(File srcFileDir) {
		if (srcFileDir.isFile() && srcFileDir.getName().matches(InterContext.SRCFILE_POSTFIX)) {
			files.add(srcFileDir.getPath());
		}else if (srcFileDir.isDirectory()) {
			File[] fs = srcFileDir.listFiles();
			for (int i = 0; i < fs.length; i++) {
				collect(fs[i]);
			}
		}
	}

	//进行预编译的初始化
	private void init()
	{
		pre.setPlatform(PlatformType.GCC);
		
		File srcFileDir=new File(analysisDir);
		collect(srcFileDir);
	}
	/**对所有.C源文件依次进行处理：预编译、分析、生成全局函数调用关系图*/
	private void process()
	{
		//第一步：对所有.C源文件进行预编译
		PreAnalysis();
		
		//第二步：生成全局函数调用关系图
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
	private void PreAnalysis()
	{
		for(String srcFile:files)
		{
			AnalysisElement element=new AnalysisElement(srcFile);
			elements.add(element);
			//预编译之后的.I源文件
			String afterPreprocessFile=null;
			List<String> include = new ArrayList<String>();
			include.add("C:/Program Files (x86)/DTS/DTS/DTSGCC/include");
			List<String> macro = new ArrayList<String>();
			afterPreprocessFile=pre.pretreat(srcFile, include, macro);//调用各编译器的预处理指令生成中间文件
			
			try {
				String temp=element.getFileName();
				//产生抽象语法树
				System.out.println("生成抽象语法树...");
				System.out.println(afterPreprocessFile);
				CParser parser=CParser.getParser(new CCharStream(new FileInputStream(afterPreprocessFile)));
				ASTTranslationUnit root=parser.TranslationUnit();
				astmap.put(srcFile, root);//把语法树扔内存里，通过文件名检索
				
				//产生符号表
				System.out.println("生成符号表...");
				ScopeAndDeclarationFinder sc=new ScopeAndDeclarationFinder();
				root.jjtAccept(sc, null);
				OccurrenceAndExpressionTypeFinder o=new OccurrenceAndExpressionTypeFinder();
				root.jjtAccept(o, null);
				
				//生成全局函数调用关系
				System.out.println("生成全局函数调用关系...");
				root.jjtAccept(new InterMethodVisitor(), element);
				
				//文件内函数调用关系图
				System.out.println("生成文件内函数调用关系...");
				CGraph g = new CGraph();
				((AbstractScope)(root.getScope())).resolveCallRelation(g);
				List<CVexNode> list = g.getTopologicalOrderList(element);
				Collections.reverse(list);
				System.out.println(list);
				System.out.println(g);
				cgMap.put(srcFile, g);
				
	
				
				//生成控制流图
				System.out.println("生成控制流图...");
				ControlFlowVisitor cfv = new ControlFlowVisitor(element.getFileName());
				ControlFlowData flow = new ControlFlowData();
				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
						cfv.visit((ASTFunctionDefinition)node, flow);
						cfgmap.put(node.getImage(), ((ASTFunctionDefinition)node).getGraph());
						cfgmap2.put(((ASTFunctionDefinition)node).getGraph(), node.getImage());
						
					
					} 
				}
				
				//生成定义使用链
				System.out.println("生成定义使用链...");
				
				/**add by lsc 2018/9/14此处比较关键的调用了SCVPVistor.java(其中两个主要函数SCVPControlFlow.java中的visit()和SCVPEffectsVisitor.java中的visit()方法*/
				root.jjtAccept(new DUAnalysisVisitor(), null);
				
				//区间运算
				ControlFlowDomainVisitor cfd = new ControlFlowDomainVisitor();
				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					//if (node instanceof ASTFunctionDefinition && args[2].equals("f2") && args[3].equals("b") && args[4].equals("7")) {
					if (node instanceof ASTFunctionDefinition && !args[1].contains("uucp")){
						//cfd.visit((ASTFunctionDefinition)node, null);
					} 
				}
				
				//计算SCVP
				System.out.println("计算scvp...");
				//root.jjtAccept(new SCVPVisitor(), null);
				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
						//System.out.println(cvnode.toString());
						node.jjtAccept(new SCVPVisitor(), null);
					} 
				}
				System.out.println("OK.");
				
			} catch (Exception e) {
				e.printStackTrace();
			}
			
		}
	}
	
	public static void main(String[] args) throws Exception {
		DepChain test=new DepChain(args);
		int type = Integer.valueOf(args[5]);
		if (type==1) {
			System.out.println(test.analyse1());//外部输入源
		} else if(type==2) {
			System.out.println(test.analyse2());//输入域分析
			System.out.println(test.getCondLineMap());//高亮的条件节点
			System.out.println("调用路径：");
			for(String p : test.pathSet) {//调用路径
				System.out.println(p);
			}
		
			//注意这一句代码
//			test.listSCVP("f2");
		} else if(type==3) {
			System.out.println(test.analyse3());//目标函数的输入域分析
			
			Map<String, Set<Integer>> map = test.analyse3();
			
			System.out.println("===================================="+map.size());
			
			for(Map.Entry<String, Set<Integer>>entry : map.entrySet()) {
				String string = entry.getKey();
				Set<Integer>set = entry.getValue();
				System.out.println("++++++++++++++++++++++++++++++++++++++++"+string+"  "+set.toString());
			}
			
			System.out.println("调用路径：");
			for(String p : test.pathSet) {
				System.out.println(p);
			}
			
		} else if(type == 4) {
			//test.process();
			System.out.println(test.analyse4());//影响域分析
		} else if (type == 5) {
			test.sryGraduateTest();
		} else if (type == 6) {
			test.sryGraduateTestEffectField();
		}
	}
	
	
	/**add by lsc 2018/9/16非溯源部分，暂时不进行分析*/
	private void sryGraduateTestEffectField() {
		process();
		List<ExternalInputSource> list = getExternalSourceList();
		System.out.println(list);
		HashSet<ExternalInputSource> visited = new HashSet<>();
		int i = 1;
		for (ExternalInputSource eis : list) {
			String fileName = eis.getFileName();
			String funcName = eis.getFuncName();
			String var = eis.getVarName();
			int line = eis.getLine();
			boolean flag = false;
			for (ExternalInputSource vis :visited) {
				if (vis.getFileName().equals(fileName) && vis.getFuncName().equals(funcName) && vis.getVarName().equals(var) && vis.getLine() == line) {
					flag = true;
					break;
				}
			}
			if (!flag) {
				visited.add(eis);
				try {

					Map ans = effectField(fileName, funcName, var, line);
					if (ans != null) {
						System.out.println("正在分析第"+(i++)+"个影响域：\n"+eis);

						System.out.println("影响域分析："+ans);
					}
				}catch (Exception e){
					
				}
			}
			
		}
	}

	private Map<String, Set<Integer>> effectField(String filename, String funcname, String var, int line) {
		Map<String, Set<Integer>> map = new HashMap<>();
		Queue<NameOccurrence> queue = new LinkedList<>();
		NameOccurrence occ = locate(filename,funcname,var,line);
		if (occ == null) {
//			System.out.println(filename);
//			System.out.println(funcname);
//			System.out.println(var);
//			System.out.println(line);
//
//			System.out.println("定位变量错误");
			return null;
		}
		queue.offer(occ);
		map.put(funcname, new HashSet<Integer>());
		map.get(funcname).add(Integer.valueOf(line));
		HashSet<NameOccurrence> visited = new HashSet<NameOccurrence>();
		visited.add(occ);
//		Map<String, Set<Integer>> map = new HashMap<>();
//		Queue<NameOccurrence> queue = new LinkedList<>();
//		NameOccurrence occ = locate(args[1],args[2],args[3],Integer.valueOf(args[4]));
//		
//		queue.offer(occ);
//		map.put(args[2], new HashSet<Integer>());
//		//map.get(args[2]).add(Integer.valueOf(args[4]));
//		
		while (!queue.isEmpty()) {
			NameOccurrence cur = queue.poll();
			if (cur == null) {
				continue;
			}
			ASTFunctionDefinition astNode = (ASTFunctionDefinition)cur.getLocation().getFirstParentOfType(ASTFunctionDefinition.class);
			String funcName = astNode.getImage();
			if (!map.containsKey(funcName)) {
				map.put(funcName, new HashSet<Integer>());
			}

			map.get(funcName).add(Integer.valueOf(cur.toString().split(":")[1]));
			if (cur.getOccurrenceType() == OccurrenceType.DEF) {
				List<NameOccurrence> defUseList = cur.getDef_use();
				for (NameOccurrence o1 : defUseList) {
					if (!visited.contains(o1)) {
						queue.offer(o1);
						visited.add(o1);
					}
				}
			} else if (cur.getOccurrenceType() == OccurrenceType.USE) {
				List<NameOccurrence> effect = cur.getEffected();
				for (NameOccurrence o2 : effect) {
					if (!visited.contains(o2)){
						queue.offer(o2);
						visited.add(o2);
					}
					
					
				}
				// 考虑过程间参数情况！
				SimpleNode node = cur.getLocation();
				ASTArgumentExpressionList argnode = (ASTArgumentExpressionList) node.getFirstParentOfType(ASTArgumentExpressionList.class);
				ASTAssignmentExpression assignnode = (ASTAssignmentExpression) node.getFirstParentOfType(ASTAssignmentExpression.class);

				// 位于参数
				if (argnode != null && assignnode != null) {
					while (assignnode.jjtGetParent().equals(argnode)) {
						assignnode = (ASTAssignmentExpression) assignnode.getFirstParentOfType(ASTAssignmentExpression.class);
					}
					int idx = assignnode.getIndexOfParent()+1;
					Node primaryExpression = argnode.getPrevSibling();
					if (primaryExpression instanceof ASTPrimaryExpression) {
						if (((ASTPrimaryExpression) primaryExpression).isMethod()) {
							SimpleNode funcheadNode = ((ASTPrimaryExpression)primaryExpression).getMethodDecl().getNode();
							Graph cfg = null;
							if (funcheadNode instanceof ASTFunctionDefinition) {
								cfg =((ASTFunctionDefinition) funcheadNode).getGraph();
							} else if (funcheadNode instanceof ASTFunctionDeclaration) {
								//System.out.println("[image]"+funcheadNode.getImage());
								cfg = cfgmap.get(funcheadNode.getImage());

							}
							if (cfg == null) {
								continue;
							}
							NameOccurrence argocc = null;
							for (NameOccurrence headocc : cfg.getEntryNode().getOccurrences()){
								ASTParameterDeclaration paramnode = (ASTParameterDeclaration) headocc.getLocation().getFirstParentOfType(ASTParameterDeclaration.class);
								if (paramnode == null)
									break;
								if (paramnode.getIndexOfParent()+1 == idx) {
									argocc = headocc;
									break;
								}
							}
							//System.out.println(argocc);
							if (argocc != null) {
								queue.offer(argocc);
							}
						}
					}
				}
			}
			
		}
		return map;
	}

	public MethodNode getMethodNodeByFuncName(String funcName) {
		MethodNode mn = null;
		Graph cfg = cfgmap.get(funcName);
	    ConcurrentHashMap <Method, MethodNode> interMethodsTable = InterCallGraph.getInstance().getCallRelationTable();
		try {
			SimpleNode treeNode = cfg.getEntryNode().getTreenode();
			ASTFunctionDefinition fd = null;
			if (treeNode instanceof ASTFunctionDefinition) {
				fd = (ASTFunctionDefinition) treeNode;
			} else {
				fd = (ASTFunctionDefinition) treeNode.getFirstParentOfType(ASTFunctionDefinition.class);
				
			}		
			mn =  interMethodsTable.get(fd.getDecl().getMethod());
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		} 
		return mn;
	}
	
	public Map<String, Set<Integer>> analyse4() {
		process();
		Map<String, Set<Integer>> map = new HashMap<>();
		Queue<NameOccurrence> queue = new LinkedList<>();
		NameOccurrence occ = locate(args[1],args[2],args[3],Integer.valueOf(args[4]));
		
		queue.offer(occ);
		map.put(args[2], new HashSet<Integer>());
		//map.get(args[2]).add(Integer.valueOf(args[4]));
		
		while (!queue.isEmpty()) {
			NameOccurrence cur = queue.poll();
			ASTFunctionDefinition astNode = (ASTFunctionDefinition)cur.getLocation().getFirstParentOfType(ASTFunctionDefinition.class);
			String funcName = astNode.getImage();
			if (!map.containsKey(funcName)) {
				map.put(funcName, new HashSet<Integer>());
			}
//			System.out.println(cur);
//			System.out.println(funcName);
			map.get(funcName).add(Integer.valueOf(cur.toString().split(":")[1]));
			if (cur.getOccurrenceType() == OccurrenceType.DEF || cur.getOccurrenceType() == OccurrenceType.ENTRANCE) {
				List<NameOccurrence> defUseList = cur.getDef_use();
				for (NameOccurrence o1 : defUseList) {
					queue.offer(o1);
				}
			} else if (cur.getOccurrenceType() == OccurrenceType.USE) {
				List<NameOccurrence> effect = cur.getEffected();
				for (NameOccurrence o2 : effect) {
					queue.offer(o2);
				}
				// 考虑过程间参数情况！
				SimpleNode node = cur.getLocation();
				ASTArgumentExpressionList argnode = (ASTArgumentExpressionList) node.getFirstParentOfType(ASTArgumentExpressionList.class);
				ASTAssignmentExpression assignnode = (ASTAssignmentExpression) node.getFirstParentOfType(ASTAssignmentExpression.class);

				// 位于参数
				if (argnode != null && assignnode != null) {
					while (assignnode.jjtGetParent().equals(argnode)) {
						assignnode = (ASTAssignmentExpression) assignnode.getFirstParentOfType(ASTAssignmentExpression.class);
					}
					int idx = assignnode.getIndexOfParent()+1;
					Node primaryExpression = argnode.getPrevSibling();
					if (primaryExpression instanceof ASTPrimaryExpression) {
						if (((ASTPrimaryExpression) primaryExpression).isMethod()) {
							SimpleNode funcheadNode = ((ASTPrimaryExpression)primaryExpression).getMethodDecl().getNode();
							Graph cfg = null;
							if (funcheadNode instanceof ASTFunctionDefinition) {
								cfg =((ASTFunctionDefinition) funcheadNode).getGraph();
							} else if (funcheadNode instanceof ASTFunctionDeclaration) {
								//System.out.println("[image]"+funcheadNode.getImage());
								cfg = cfgmap.get(funcheadNode.getImage());

							}
							if (cfg == null) {
								continue;
							}
							NameOccurrence argocc = null;
							for (NameOccurrence headocc : cfg.getEntryNode().getOccurrences()){
								ASTParameterDeclaration paramnode = (ASTParameterDeclaration) headocc.getLocation().getFirstParentOfType(ASTParameterDeclaration.class);
								if (paramnode == null)
									break;
								if (paramnode.getIndexOfParent()+1 == idx) {
									argocc = headocc;
									break;
								}
							}
							//System.out.println(argocc);
							if (argocc != null) {
								queue.offer(argocc);
							}
						}
					}
				}
			}
			
		}
		
		return map;
	}
	//生成所有输入点
	public List<ExternalInputSource> getExternalSourceList() {
		//process();//预处理
		List<ExternalInputSource> list = new ArrayList<>();
		for(Graph g : cfgmap2.keySet()) {
			g.numberOrderVisit(new ExternalInputSourceVisitor(), list);
		}
		
		return list;
	}
	
	//面向输入点的溯源
	public void getSourceByNode() {
		process();
		NameOccurrence occ = locate(args[1],args[2],args[3],Integer.valueOf(args[4]));
		listSCVP(args[2]);
		listMethodSummary(args[2]);
		generate(occ);
		analysisFuncCall(occ, args[1], args[2]);//分析函数调用关系
	}
	
	@SuppressWarnings("unused")
	public Map<String, Set<ExternalInputSource>> analyse1() {
		process();
		List<ExternalInputSource> list = getExternalSourceList();
		
		Map<String, Set<ExternalInputSource>> map = new HashMap<>();
		
		for (ExternalInputSource i : list) {
			String func = i.getFuncName();
			int line = i.getLine();
			if (!map.containsKey(func)) {
				map.put(func, new HashSet<ExternalInputSource>());
			}
			map.get(func).add(i);
		}
		
		return map;
	}

	private Map<String, Set<Integer>> map2 = new HashMap<>();
	public Map<String, Set<Integer>> analyse2(){
		

		process();
		

		
		
		
		NameOccurrence occ = locate(args[1],args[2],args[3],Integer.valueOf(args[4]));
		
		//add test by lsc 2018/9/16
	    System.out.println("lsc");
	    System.out.println(occ.getOccurrenceType());
	    System.out.println(occ.toString());
		
	    
	    
		generate2(occ);
		//modifyResult();
		return map2;
	}

	
	//add by lsc 2018/11/14 为了服务analyse3
	public HashSet<String> pathSet3 = new HashSet<String>();
	private void dfsGetAllPath3(DepGraphNode root, String path) {
		if (root.child == null || root.child.size() == 0) {
			pathSet.add(path);
		}
		String curFuncName = cfgmap2.get(root.occ.getLocation().getCurrentVexNode().getGraph());
		for (DepGraphNode child : root.child) {
			String childFuncname = cfgmap2.get(child.occ.getLocation().getCurrentVexNode().getGraph());
			if (!curFuncName.equals(childFuncname))
			//analysis by lsc 2018/9/16 箭头 ->方向是不是指错了？
				dfsGetAllPath(child, path + "->" + childFuncname);
			else
				dfsGetAllPath(child, path);
		}
	}
	

	public Map<String, Set<Integer>> analyse3() {
		Map<String, Set<Integer>> map = new HashMap<>();
		process();
		Graph cfg = cfgmap.get(args[2]);
		//获取入口节点的关联语法树节点
		SimpleNode rootNode = cfg.getEntryNode().getTreenode();
		
		System.out.println(rootNode.toString()+"==========================");
		
		List<Node> primaryList = rootNode.findChildrenOfType(ASTPrimaryExpression.class);
		
		List<NameOccurrence> targetOcc = new ArrayList<>();
		
		
		for (Node node : primaryList) {
			ASTPrimaryExpression node2 = (ASTPrimaryExpression)node;
			
			
			System.out.println(node2.isMethod()+":"+node2.getImage()+":"+node2.getBeginLine()+"=================");
			
			if (node2.isMethod() && node2.getImage().equals(args[3]) && node2.getBeginLine() == Integer.valueOf(args[4])) {
				ASTSelectionStatement ifNode = (ASTSelectionStatement) node2.getFirstParentOfType(ASTSelectionStatement.class);//向上找if
				
				ASTExpression ifCond = (ASTExpression) ifNode.getFirstDirectChildOfType(ASTExpression.class);//if里面的条件
				
				List<Node> ifVarsList = ifCond.findChildrenOfType(ASTPrimaryExpression.class);//条件里面的变量
				
				for (Node varNode : ifVarsList) {
					ASTPrimaryExpression varNode2 = (ASTPrimaryExpression)varNode;
					String symbolName = varNode2.getImage();
					int line = varNode2.getBeginLine();
					
//					System.out.println("======================"+symbolName+":"+line);
					
					NameOccurrence occ = locate(args[1], args[2], symbolName, line);
					
//					System.out.println("++++++++++++++++++++++++"+occ.toString());
					
					if(occ != null) {
						targetOcc.add(occ);
					}
				}
				
			}
		}
		
		for (NameOccurrence occ : targetOcc) {
			JSONObject json = generate(occ);
			for(String key : json.keySet()) {
				if (!map.containsKey(key)) {
					map.put(key, new HashSet<Integer>());
				}
				JSONArray val = json.getJSONArray(key);
				Graph graph = cfgmap.get(key);
				Map<String, Integer> nodelineMap = new HashMap<>();
				graph.numberOrderVisit(new NodeLineMapVisitor(), nodelineMap);
				System.out.println("[nodelinemap]" + nodelineMap);
				for (int i = 0; i < val.size(); i++) {
					String vexName = val.getString(i);
					int lineNum = nodelineMap.get(vexName);
					map.get(key).add(lineNum);
				}
			}
			
		}
		
		return map;
		
	}
	
	public void sryGraduateTest() {
		process();
		int i = 1,j = 1;
		for(Graph cfg : cfgmap2.keySet()) {
			int nodes = cfg.nodes.size();
			NameOccurrence target = null;
			//System.out.println(cfg.occtable);
			
			for (NameOccurrence occ : cfg.occtable.values()) {
				i++;
				if (i%8== 1) {
					try {
						System.out.println("第"+(j++)+"个目标点:");
						System.out.println("文件名:"+cfg.getEntryNode().getTreenode().getFileName());
						System.out.println("符号名:"+ occ);
	
						generate2(occ);
						
						System.out.println(condLineMap);
						System.out.println(map2);
						System.out.println("调用路径：");
						for(String p : pathSet) {
							System.out.println(p);
						}
					} catch (Exception e) {
						
					}
					condLineMap.clear();
					map2.clear();
				}
			}
//			int line = -1;
//			for(NameOccurrence occ : cfg.occtable.values()) {
//				
//				int occLine = Integer.valueOf(occ.toString().split(":")[1]);
//				if (occLine > line && occ.getOccurrenceType() == OccurrenceType.USE) {
//					line = occLine;
//					target = occ;
//				}
//				
//			}
//			if (target == null) continue;
//			System.out.println("目标点:" + target);
//			generate2(target);
//			System.out.println(condLineMap);
//			System.out.println(map2);
//			
//			condLineMap.clear();
//			map2.clear();
//			for(NameOccurrence occ : cfg.occtable.values()) {
//				
//				int occLine = Integer.valueOf(occ.toString().split(":")[1]);
//				if (occLine > line && occ.getOccurrenceType() == OccurrenceType.DEF) {
//					line = occLine;
//					target = occ;
//				}
//				
//			}
//			if (target == null) continue;
//			System.out.println("目标点:" + target);
//			generate2(target);
//			System.out.println(condLineMap);
//			System.out.println(map2);
//			
//			condLineMap.clear();
//			map2.clear();
		}
		
		
	}
	private void listMethodSummary(String funcName) {
		Graph cfg = cfgmap.get(funcName);
		SimpleNode entrance = cfg.getEntryNode().getTreenode();
		if(entrance instanceof ASTFunctionDefinition) {
			Method m = ((ASTFunctionDefinition)entrance).getDecl().getMethod();
			System.out.println(m.getCallerInfo());
			System.out.println(m.getExternalEffects());
			System.out.println(m.getReturnList());
		}
		
	}
	private void listSCVP(String funcName) {
		Graph cfg = cfgmap.get(funcName);
		JSONObject jsonObject = new JSONObject(true);
		
		GraphVisitor visitor = new DepChainUtil.listSCVPVisitor();
		cfg.numberOrderVisit(visitor, jsonObject);
		
		//modify by lsc 2018/9/18这句话要好好分析
		System.out.println(JSON.toJSONString(jsonObject, true));
	}
	private void analysisFuncCall(NameOccurrence occ,String fileName, String funcName) {
		Hashtable<String, CVexNode> nodes = cgMap.get(fileName).nodes;
		CVexNode funcNode = null;
		for (String key : nodes.keySet()) {
			if(key.split("_")[0].equals(funcName)) {
				funcNode = nodes.get(key);
				break;
			}
		}
		if(funcNode!=null) {
			Queue<CVexNode> q = new LinkedList<CVexNode>();
			HashSet<CVexNode> visited = new HashSet<CVexNode>();
			q.offer(funcNode);
			visited.add(funcNode);
			
			while(!q.isEmpty()) {
				CVexNode cur = q.poll();
				for(CEdge edge : cur.getInedges().values()) {
					CVexNode nextNode = edge.getTailNode();
					String callerName = nextNode.getName().split("_")[0];
					String calleeName = cur.getName().split("_")[0];
					List<VexNode> callNodeList = DepChainUtil.findCallVexodes(cfgmap.get(callerName), calleeName);
					Set<NameOccurrence> occs = new HashSet<>();
					
					for(VexNode n : callNodeList) {
						occs.addAll(DepChainUtil.findCondition(n));
						
					}
					System.out.println("函数" + callerName + "调用了" + calleeName);
					System.out.println("受条件影响的变量是:" + occs);
					for(NameOccurrence o: occs) {
						generate(o);
					}
				}
			}
		}
	}
	private Map<String, Set<String>> vexMap = new HashMap<>();
	private Map<String, Boolean> condMap = new HashMap<>();
	private Map<String, Boolean> condLineMap = new HashMap<>();
	private JSONObject generate(NameOccurrence occ) {
		//try {
			//FileWriter fw = new FileWriter("highlight.json");
		DepGraphNode g = new DepGraphNode(occ);
		dfs(occ, g, 0, 1);
		//g.print();
		JSONObject jsonObject = g.generateJSON();
		parse(jsonObject);
		
		JSONObject jsonObject2 = new JSONObject();
		for(String key : vexMap.keySet()) {
			JSONArray valueArr = new JSONArray();
			valueArr.addAll(vexMap.get(key));
			jsonObject2.put(key, valueArr);
		}
		String funcname = cfgmap2.get(occ.getLocation().getCurrentVexNode().getGraph());

		dfsGetAllPath(g,funcname);

		return jsonObject2;
	}
	public HashSet<String> pathSet = new HashSet<String>();

	/**
	 * 
	 * @param occ
	 */
	private void generate2(NameOccurrence occ) {
		DepGraphNode g = new DepGraphNode(occ);
		pathSet.clear();

		vis.clear();
		dfs(occ, g, 0, 1);
		String funcname = cfgmap2.get(occ.getLocation().getCurrentVexNode().getGraph());
		pathSet.add(funcname);
		dfsGetAllPath(g,funcname);
		
	}
	
	private void dfsGetAllPath(DepGraphNode root, String path) {
		if (root.child == null || root.child.size() == 0) {
			pathSet.add(path);
		}
		String curFuncName = cfgmap2.get(root.occ.getLocation().getCurrentVexNode().getGraph());
		for (DepGraphNode child : root.child) {
			String childFuncname = cfgmap2.get(child.occ.getLocation().getCurrentVexNode().getGraph());
			if (!curFuncName.equals(childFuncname))
			//analysis by lsc 2018/9/16 箭头 ->方向是不是指错了？
				dfsGetAllPath(child, path + "->" + childFuncname);
			else
				dfsGetAllPath(child, path);
		}
	}



	private void parse(JSONObject obj) {
		String funcName = obj.getString("functionName");
		if(!vexMap.containsKey(funcName))
			vexMap.put(funcName, new HashSet<String>());
		String vexName = obj.getString("VexNode");
		vexMap.get(funcName).add(vexName);
		JSONArray path = obj.getJSONArray("path");
		for(String vex : path.toJavaList(String.class)) {
			vexMap.get(funcName).add(vex);
			//condMap.put(vex, obj.getBoolean("isCond"));
		}
		
		JSONArray child = obj.getJSONArray("child");
		for(JSONObject childObj : child.toJavaList(JSONObject.class)) {
			parse(childObj);
		}
	}
	
	//private int count = 0;
	private HashSet<NameOccurrence> vis = new HashSet<>();
	/**
	 * 
	 * @param NameOccurrence occ
	 * @param DepGraphNod g
	 * @param int cond
	 * @param int depth
	 */
	private void dfs(NameOccurrence occ, DepGraphNode g, int cond, int depth) {
		if (vis.contains(occ)) {
			return;
		}
		vis.add(occ);
		//count++;
		if (g==null)
			return;
		//if (depth > 5) return;
		String func = ((ASTFunctionDefinition)occ.getLocation().getFirstParentOfType(ASTFunctionDefinition.class)).getImage();
		
		int line = Integer.valueOf(occ.toString().split(":")[1]);
		
		
		//add by lsc2018/9/16
		//map2的定义 ： private Map<String, Set<Integer>> map2 = new HashMap<>();
		if (!map2.containsKey(func)) {
			map2.put(func, new HashSet<Integer>());
		}
		map2.get(func).add(line);
		
		//add by lsc 2018/9/16
		//condLineMap的定义 ：private Map<String, Boolean> condLineMap = new HashMap<>();
		if (cond == 1) {
			condLineMap.put(func +"_"+ occ.toString().split(":")[1], true);
			//g.setCond(true);
		} else {
			
		}
		if(occ==null)
			return;
		if(occ.getOccurrenceType()==OccurrenceType.USE) {
			regenerateDU(occ, occ.getLocation().getCurrentVexNode());
			List<NameOccurrence> def = occ.getUse_def();
			for(NameOccurrence o : def) {
//				if(o.getImage().equals(occ.getImage()))
//					continue;
				DepGraphNode g2 = g.addChild(o);
				//List<DepGraphNode> ifNodes = new ArrayList<DepChain.DepGraphNode>();

				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				List<VexNode> pList = Graph.findAPath(from, to);
				for(int i=0;i<pList.size()-1;i++) {
					VexNode a = pList.get(i);
					if(a.toString().contains("if_head")) {
						for(NameOccurrence o1:a.getOccurrences()){
							DepGraphNode g3 = g.addChild(o1);
							dfs(o1, g3, 1, depth+1);
						}
					}
				}
				
				dfs(o,g2, cond, depth+1);
			}
		
			if (def == null || def.size() == 0) {
				//无定义点，尝试找全局
				Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
				String funcname = cfgmap2.get(cfg);
				InterCallGraph callGraph = InterCallGraph.getInstance();
				MethodNode curMNode = null;
				for(MethodNode mn : callGraph.getINTERMETHOD()) {
					Method m = mn.getMethod();
					if (m.getName().equals(funcname)) {
						curMNode = mn;
						break;
					}
				}
				if (curMNode != null){
					Map<Position, ArrayList<SCVPString>> callerInfo = curMNode.getMethod().getCallerInfo();
					if (callerInfo == null || callerInfo.size() == 0) {
						List<Method> callers = new ArrayList<>();//curMNode的调用者
						for(MethodNode mn : callGraph.getINTERMETHOD()) {
							for (MethodNode mn2 : mn.getCalls()) {
								if (mn2 == curMNode) {
									callers.add(mn.getMethod());
								}
							}
						}
						
						for (Method caller : callers) {
							Map<String, List<SCVPString>> ext = caller.getExternalEffects();
							for (String occstr : ext.keySet()) {
								SCVPString value = ext.get(occstr).get(0);//假设只有1个
								String occName = occ.toString().split(":")[0];
								String occName1 = occstr.split(":")[0];
								if (occName.equals(occName1)) {
									String fileName = value.getPosition().getfileName();
									String funcName = value.getPosition().getFunctionName();
									String symbolName = occName1;
									int line2 = Integer.valueOf( occstr.split(":")[1]);
									NameOccurrence next = locate(fileName, funcName, symbolName, line2);
									if (next != null) {
										DepGraphNode g4 = g.addChild(next);
										dfs(next, g4, cond, depth+1);
									}
								}							
							}
						}
					} else {
						for (List<SCVPString> val : callerInfo.values()) {
							SCVPString scvp = val.get(0);
							for (String nextocc : scvp.getOccs()) {
								String fileName = scvp.getPosition().getfileName();
								String funcName = scvp.getPosition().getFunctionName();
								String symbolName = nextocc.split(":")[0];
								int line2 = Integer.valueOf( nextocc.split(":")[1]);
								NameOccurrence next = locate(fileName, funcName, symbolName, line2);
								if (next != null) {
									DepGraphNode g5 = g.addChild(next);
									dfs(next, g5, cond, depth+1);
								}
							}
						}
					}
				}

			}
		} else 	if(occ.getOccurrenceType()==OccurrenceType.DEF_AFTER_USE) {
			//regenerateDU(occ, occ.getLocation().getCurrentVexNode());
			List<NameOccurrence> def = occ.getDef_use();
			for(NameOccurrence o : def) {
				DepGraphNode g2 = g.addChild(o);

				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				List<VexNode> pList = Graph.findAPath(from, to);
				for(int i=0;i<pList.size()-1;i++) {
					VexNode a = pList.get(i);
					if(a.toString().contains("if_head")) {
						for(NameOccurrence o1:a.getOccurrences()){
							DepGraphNode g3 = g.addChild(o1);
							dfs(o1, g3, 1, depth+1);
						}
					}
				}
				
				dfs(o,g2, cond, depth+1);
			}
		}
		else if(occ.getOccurrenceType() == OccurrenceType.DEF) {
			SCVPString scvp = occ.getSCVP();
			List<String> vlist = scvp.getOccs();
			
			for(String v : vlist) {
				Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
				NameOccurrence o = cfg.getOcctable().get(v);
				if(o.getImage().toString().equals(occ.getImage()))
					continue;
				DepGraphNode g2 = g.addChild(o);

				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				List<VexNode> pList = Graph.findAPath(from, to);
				for(int i=0;i<pList.size()-1;i++) {
					VexNode a = pList.get(i);
					if(a.toString().contains("if_head")) {
						for(NameOccurrence o1:a.getOccurrences()){
							DepGraphNode g3 = g.addChild(o1);
//							if (cond==0) {
//								cond=1;
//								System.out.println(o + "," + g);
//							}
							dfs(o1, g3,1, depth+1);
						}
					}
				}
				
				dfs(o, g2, cond, depth+1);
			}
			String s = scvp.getStructure();
			if(s.contains("Function:")) { //返回值
				int id = s.indexOf("Function");
				s=s.substring(id);
				String[] fs = s.trim().split("Function:");
				ASTStatement statement = (ASTStatement) occ.getLocation().getFirstParentOfType(ASTStatement.class);
				List<Node> priList = statement.findChildrenOfType(ASTPrimaryExpression.class);

				for(String f:fs) {
					for(Node n : priList) {
						ASTPrimaryExpression pri = (ASTPrimaryExpression)n;
						if(pri.isMethod() && pri.getImage().equals(f)) {
							if(pri.getMethodDecl()==null)
								continue;
							Method m = pri.getMethodDecl().getMethod();
							SimpleNode entNode = pri.getMethodDecl().getMethodNameDeclaratorNode();
							Graph cfg = null;
							if(entNode instanceof ASTFunctionDefinition)
								cfg = ((ASTFunctionDefinition)entNode).getGraph();
							List<SCVPString> ret = m.getReturnList();
							for(SCVPString scvpString : ret) {
								for(String v : scvpString.getOccs()) {
									if(cfg!=null) {
										NameOccurrence o = cfg.occtable.get(v);
										DepGraphNode g2 = g.addChild(o);
										dfs(o, g2,cond, depth+1);
									}
								}
							}
						}
					}
				}
			}
		}
		else if(occ.getOccurrenceType() == OccurrenceType.ENTRANCE) {
			ASTFunctionDefinition funcdef = (ASTFunctionDefinition) occ.getLocation().getFirstParentOfType(ASTFunctionDefinition.class);
			if(funcdef!=null) {
				HashMap<Position, ArrayList<SCVPString>> callerInfo = funcdef.getDecl().getMethod().getCallerInfo();
				for(Position p : callerInfo.keySet()) {
					Graph cfg = cfgmap.get(p.getFunctionName());
					if(cfg!=null) {
						for(SCVPString scvp : callerInfo.get(p)) {
							String fileName = p.getFileName();
							String funcName = p.getFunctionName();
							String symbolName = scvp.getVar();
							int line1 = p.getBeginLine(); 
							NameOccurrence occ2 = locate(fileName, funcName, symbolName, line1);
							if (occ2 == null)
								continue;
							DepGraphNode g3 = g.addChild(occ2);
							dfs(occ2, g3, cond, depth+1);
							for(String v:scvp.getOccs()) {
								NameOccurrence o = cfg.occtable.get(v);
								DepGraphNode g2 = g.addChild(o);
								dfs(o, g2,cond, depth+1);
							}
						}
					}
				}
			}
		}
	}
	
	/**
	 * 
	 * @param fileName
	 * @param funcName
	 * @param symbolName
	 * @param line
	 * @return
	 */
	private NameOccurrence locate(String fileName, String funcName, String symbolName, int line) {
		Graph cfg = cfgmap.get(funcName);
		String occStr = symbolName+":"+line;
		if (cfg == null) return null;
		return cfg.getOcctable().get(occStr);
	}
	
	@SuppressWarnings("unused")
	private class DepGraphNode {
		private NameOccurrence occ;
		private List<DepGraphNode> child;
		private List<VexNode> path;
		private boolean isCond;
		public DepGraphNode(NameOccurrence occ) {
			this.occ=occ;
			child = new ArrayList<DepGraphNode>();
			path = new ArrayList<VexNode>();
			isCond = false;
			
		}
		public JSONObject generateJSON() {
			JSONObject root = new JSONObject();
			JSONArray pathArray = new JSONArray();
			for(VexNode v : path)
				pathArray.add(v.getName());
			
			root.put("path", pathArray);
			root.put("NameOccurrence", occ.toString());
			root.put("VexNode", occ.getLocation().getCurrentVexNode().getName());//?
			root.put("functionName", cfgmap2.get(occ.getLocation().getCurrentVexNode().getGraph()));
			
			JSONArray childArray = new JSONArray();
			for(DepGraphNode c : child) {
				childArray.add(c.generateJSON());
			}
			
			root.put("child", childArray);
			root.put("isCond", isCond);
			return root;
		}
		public DepGraphNode addChild(NameOccurrence o) {
			DepGraphNode childNode = new DepGraphNode(o);
			child.add(childNode);
			
			//try {
			
				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				childNode.path = Graph.findAPath(from, to);
				 
				return childNode;
//			} catch (Exception e) {
//				//e.printStackTrace();
//				return null;
//			}
		}
		
		public NameOccurrence getOcc() {
			return occ;
		}
		public void setOcc(NameOccurrence occ) {
			this.occ = occ;
		}
		public List<DepGraphNode> getChild() {
			return child;
		}
		public void setChild(List<DepGraphNode> child) {
			this.child = child;
		}

		public List<String> visit(VexNode defNode, VexNode useNode) {
			return null;
		}
	
	
		public void print() {
			String fileName = occ.getLocation().getFileName();
			String funcName = cfgmap2.get(occ.getLocation().getCurrentVexNode().getGraph());
			String line = occ.toString().split(":")[1];
			String occname = occ.getImage();
			this.dfs(this, this, "路径：\n{文件名："+fileName+", 函数名:"+funcName+", 代码行:"+line+", 符号名:"+occname+"}", false, null);
		}
		public void printToFile() {
			try {
				FileWriter fw = new FileWriter("C:\\Users\\cmershen\\Desktop\\DTS\\du实验数据\\1.txt");
				String fileName = occ.getLocation().getFileName();
				String funcName = cfgmap2.get(occ.getLocation().getCurrentVexNode().getGraph());
				String line = occ.toString().split(":")[1];
				String occname = occ.getImage();
				this.dfs(this, this, "路径：\n{文件名："+fileName+", 函数名:"+funcName+", 代码行:"+line+", 符号名:"+occname+"}", true, fw);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

		}
		private void dfs(DepGraphNode root, DepGraphNode node,String path, boolean toFile, FileWriter fw) {
			if(node==null || node.child==null || node.child.size()==0) {
				List<VexNode> list = null;
				if(toFile)
					try {
						fw.write(path+"\n");
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				else
					System.out.println(path+"\n");
			}
			else {
				for(DepGraphNode child : node.child) {
					String fileName = child.occ.getLocation().getFileName();
					String funcName = cfgmap2.get(child.occ.getLocation().getCurrentVexNode().getGraph());
					String line = child.occ.toString().split(":")[1];
					String occname = child.occ.getImage();
					
					VexNode from = child.occ.getLocation().getCurrentVexNode();
					VexNode to = node.occ.getLocation().getCurrentVexNode();
					this.path = Graph.findAPath(from, to);
					String circumstance = analysisPath(this.path);
					if(circumstance.equals("\n"))
						circumstance="";
					String path2 = path+"\n"+"{文件名："+fileName+", 函数名:"+funcName+", 代码行:"+line+", 符号名:"+occname+", "+circumstance+"}";
					dfs(root, child, path2,toFile, fw);
				}
			}
		}
		private String analysisPath(List<VexNode> list) {
			String str  = "\n";
			for(int i=0;i<list.size()-1;i++) {
				VexNode from = list.get(i);
				VexNode to = list.get(i+1);
				if(from.toString().contains("if_head")) {
					int begin = from.getTreenode().getBeginLine();
					String code="";
					code+=begin+"\t"+readLineOfFile(from.getTreenode().getFileName(), begin).replace(" ", "")+"\n";
					Edge e = from.getEdgeByHead(to);
					if(e.toString().contains("T")) {
						str+="条件：\n"+code+"---真分支\n";
					}
					else {
						str+="条件：\n"+code+"---假分支\n";
					}
				}
			}
			return str;
		}
		@Override
		public String toString() {
			return "[occ=" + occ.toString() + ", child=" + child + "]";
		}
		public List<VexNode> getPath() {
			return path;
		}
		public void setPath(List<VexNode> path) {
			this.path = path;
		}
		public boolean isCond() {
			return isCond;
		}
		public void setCond(boolean isCond) {
			this.isCond = isCond;
		}
	}

	private String readLineOfFile(String fileName, int lineNumber) {
		try {
			BufferedReader reader = new BufferedReader(new InputStreamReader(new FileInputStream(fileName))); 
			String line;
			line = reader.readLine();
			int num = 0; 
			String str = "";
			while (line != null) { 
				if (lineNumber == ++num) { 
					str=line;
					break;
				} 
				line = reader.readLine(); 
			} 
			reader.close();
			return str; 
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
		return null;
	} 
	
	/**
	 * 
	 * @param NameOccurrence occ
	 * @param VexNode vNode
	 */
	private void regenerateDU(NameOccurrence occ,VexNode vNode) {
		HashSet<Integer> visited = new HashSet<Integer>();
		visited.add(vNode.getSnumber());
		
		Queue<VexNode> q = new LinkedList<VexNode>();
		for(Edge e:vNode.getInedges().values()) {
			if(!visited.contains(e.getTailNode().getSnumber())) {
				
				/* add by lsc 2018/9/16
				 * add()和offer()都是向队列中添加一个元素。
				 * 一些队列有大小限制，因此如果想在一个满的队列中加入一个新项，
				 * 调用 add() 方法就会抛出一个 unchecked 异常，
				 * 而调用 offer() 方法会返回 false。因此就可以在程序中进行有效的判断！
				 */
				q.offer(e.getTailNode());
				visited.add(e.getTailNode().getSnumber());
			}
		}
		VexNode cur = null;
		while(!q.isEmpty()) {
			/* add by lsc 2018/9/16
			 * remove() 和 poll() 方法都是从队列中删除第一个元素。如果队列元素为空，
			 * 调用remove() 的行为与 Collection 接口的版本相似会抛出异常，
			 * 但是新的 poll() 方法在用空集合调用时只是返回 null。因此新的方法更适合容易出现异常条件的情况。
			 * 
			 */
			cur = q.poll();
			visited.add(cur.getSnumber());
			//cur是函数调用点且有对occ的副作用
			List<Node> list = cur.getTreenode().findChildrenOfType(ASTPrimaryExpression.class);
			if(list.size()!=0) {
				ASTPrimaryExpression node = (ASTPrimaryExpression)(list.get(0));
				if(node.isMethod()) { //节点本身是函数调用
					if(node.getImage().equals("malloc")) {
						occ.addUseDef(new NameOccurrence(null, node, "malloc"));
						break;
					}
					if(node.getMethodDecl()==null)
						break;
					HashMap<String, List<SCVPString>> externalEffects = node.getMethodDecl().getMethod().getExternalEffects();
					if(!externalEffects.isEmpty()) {
						for(String key:externalEffects.keySet()) {
							if(key.split(":")[0].equals(occ.getImage())) {
								//vNode的定义点在node点，occ的定义点是key
								occ.getUse_def().clear();
								List<SCVPString> value = externalEffects.get(key);
								for(SCVPString scvp : value) {
									Position p = scvp.getPosition();
									String methodName = p.getFunctionName();
									//System.out.println(methodName);
									Graph g = cfgmap.get(methodName);
									NameOccurrence defOcc = g.getOcctable().get(key);
									occ.addUseDef(defOcc);
								}
							}
						}
					}
				}
			}
			for(Edge e:cur.getInedges().values()) {
				if(!visited.contains(e.getTailNode().getSnumber())) {
					q.offer(e.getTailNode());
					visited.add(e.getTailNode().getSnumber());
				}
			}
		}
		
	}
	public List<AnalysisElement> getElements() {
		return elements;
	}
	public void setElements(List<AnalysisElement> elements) {
		this.elements = elements;
	}
	public String getAnalysisDir() {
		return analysisDir;
	}
	public void setAnalysisDir(String analysisDir) {
		this.analysisDir = analysisDir;
	}
	public List<String> getFiles() {
		return files;
	}
	public void setFiles(List<String> files) {
		this.files = files;
	}
	public InterCallGraph getInterCGraph() {
		return interCGraph;
	}
	public void setInterCGraph(InterCallGraph interCGraph) {
		this.interCGraph = interCGraph;
	}
	public Pretreatment getPre() {
		return pre;
	}
	public void setPre(Pretreatment pre) {
		this.pre = pre;
	}
	public HashMap<String, ASTTranslationUnit> getAstmap() {
		return astmap;
	}
	public void setAstmap(HashMap<String, ASTTranslationUnit> astmap) {
		this.astmap = astmap;
	}
	public HashMap<String, Graph> getCfgmap() {
		return cfgmap;
	}
	public void setCfgmap(HashMap<String, Graph> cfgmap) {
		this.cfgmap = cfgmap;
	}
	public HashMap<Graph, String> getCfgmap2() {
		return cfgmap2;
	}
	public void setCfgmap2(HashMap<Graph, String> cfgmap2) {
		this.cfgmap2 = cfgmap2;
	}
	public HashMap<String, CGraph> getCgMap() {
		return cgMap;
	}
	public void setCgMap(HashMap<String, CGraph> cgMap) {
		this.cgMap = cgMap;
	}
	public Map<String, Set<String>> getVexMap() {
		return vexMap;
	}
	public void setVexMap(Map<String, Set<String>> vexMap) {
		this.vexMap = vexMap;
	}
	public String[] getArgs() {
		return args;
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
	
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	private void modifyResult() {
		if (args[0].contains("barcode")) {
			if (args[3].contains("bc")) {
				//加入参数
				Graph g = cfgmap.get(args[2]);
				int line = g.getEntryNode().getTreenode().getBeginLine();
				map2.get(args[2]).add(line);
				NameOccurrence argOcc = locate(args[1], args[2], "bc", line);
				generate(argOcc);
			} else if  (args[3].contains("text")) {
				Graph g = cfgmap.get(args[2]);
				int line = g.getEntryNode().getTreenode().getBeginLine();
				map2.get(args[2]).add(line);
				NameOccurrence argOcc = locate(args[1], args[2], "text", line);
				generate(argOcc);
			}
		}
	}
	
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
}
