package softtest.depchain.c;

import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Graph;
import softtest.cfg.c.VexNode;

public class FunctionGlobalVarivable {
	
	//��¼������ȫ�ֱ���������Ϣ��ȫ�ֱ���Ϊ�������������ȫ�ֱ�����
	private List<Map<VexNode,String>> list = new LinkedList<Map<VexNode,String>>();
	//�ⲿ����Դ��Ϣ��Ϊ�˷������ͼ���
	private List<String>  list_outsource = new ArrayList<String>();
	//ȫ�ֱ�����Ϣ
	public static List<List<String>> global_VariablesList = new ArrayList<>();
	//��Ŀȫ��ȫ�ֱ�������ժҪ
	public static HashMap<String,List<Map<VexNode,String>>> functionGlobal = new HashMap<String,List<Map<VexNode,String>>>() ;
	
	public FunctionGlobalVarivable(){
		
	}
	
	public void findFunctionGlobal(List<List<VexNode>> nodePaths){
		
		list.clear();		
		for(List<VexNode>path:nodePaths){
			//��¼��ǰ·����������Ľڵ�
			List<VexNode> defNode = new ArrayList<VexNode>();
			//��¼��ǰ·������ֵ�ı�Ľڵ�
			List<VexNode> useNode = new ArrayList<VexNode>();
			//��¼�������
			VexNode headNode = null;
			//��¼��ǰ·������
			List<String> defValue = new ArrayList<String>();
			//��¼��ǰ·������ֵ
			List<String> useValue = new ArrayList<String>();
			
			//����������Ҫ�ڵ�����
			for(VexNode node:path){
				
				String type = VexNodeType.getVexNodeType(node,list_outsource);
				
				if(type == VexNodeType.TYPE_2.name() || type == VexNodeType.TYPE_3.name() ){
					defNode.add(node);
				}
				
				if(type == VexNodeType.TYPE_4.name()){
					useNode.add(node);
				}
				
				if(type == VexNodeType.TYPE_0.name()){
					headNode = node;
				}
				
			}
			//��ȡ�ڵ�������
			for(VexNode node:defNode){
				SimpleNode simpleNode = node.getTreenode();
				for(String str : ergodicAst(simpleNode) )
				defValue.add(str);
			}
			
			if(headNode != null){
				List<String> str = ergodicHAst(headNode.getTreenode());
				for(String temStr:str){
					defValue.add(temStr);
				}
			}
			for(VexNode node:useNode){
				SimpleNode simpleNode = node.getTreenode();
				useValue.add(ergodicPAst(simpleNode));
			}
			
			//Ѱ��ȫ�ֱ�����
			for(int i = 0; i < useValue.size();i++){
				  if(!defValue.contains(useValue.get(i))){
					  boolean flg = false;
					  for(Map<VexNode, String>  map : list){
						  if(map.containsValue(useValue.get(i))){
							  flg = true;
							  break;
						  }
					  }
					  if(!flg){
						  Map<VexNode,String> map = new HashMap<VexNode,String>();
						  map.put(useNode.get(i), useValue.get(i));
						  list.add(map);
					  }
					  
					  
				  }
			}
			
			
			
		}
		
		compareGlobal();
	}
	
	private List<String> ergodicAst(SimpleNode root){
		
		Stack<SimpleNode> stack = new Stack<SimpleNode>();
		List<String> list = new ArrayList<String>();
		stack.push(root);
		
		while(!stack.isEmpty()){
			SimpleNode tem = stack.pop();
			
			for(int i=0;i<tem.jjtGetNumChildren();i++){
				
				if(tem.jjtGetChild(i) instanceof ASTDirectDeclarator){
					SimpleNode s = (SimpleNode) tem.jjtGetChild(i);
					list.add( s.getImage() );
				}else{
					stack.push((SimpleNode) tem.jjtGetChild(i));
				}
			}
		}
		return list;
		
	}
	
    private String ergodicPAst(SimpleNode root){
		
		List<SimpleNode> list = new ArrayList<SimpleNode>();
		list.add(root);
		
		while(!list.isEmpty()){
			SimpleNode tem = list.remove(0);
			
			for(int i=0;i<tem.jjtGetNumChildren();i++){
				
				if(tem.jjtGetChild(i) instanceof ASTPrimaryExpression){
					SimpleNode s = (SimpleNode) tem.jjtGetChild(i);
					return s.getImage();
				}else{
					list.add((SimpleNode) tem.jjtGetChild(i));
				}
			}
		}
		return null;
		
	}
    
    //����������ڲ���
    	private List<String> ergodicHAst(SimpleNode root){
    		
    	 List<String> hString = new ArrayList<String>();
         for(int i = 0; i < root.jjtGetNumChildren();i++){
        	 if(root.jjtGetChild(i) instanceof ASTDeclarator){
        		 root = (SimpleNode) root.jjtGetChild(i);
        	 }
         }
		
		Stack<SimpleNode> stack = new Stack<SimpleNode>();
		stack.push(root);
		
		while(!stack.isEmpty()){
			SimpleNode tem = stack.pop();
			
			for(int i=0;i<tem.jjtGetNumChildren();i++){
				
				if(tem.jjtGetChild(i) instanceof ASTDirectDeclarator){
					SimpleNode s = (SimpleNode) tem.jjtGetChild(i);
					hString.add(s.getImage());
					if(s.jjtGetNumChildren()>0){
						stack.push(s);
					}
				}else{
					stack.push((SimpleNode) tem.jjtGetChild(i));
				}
			}
		}
		
		if(hString.size()>0){
			hString.remove(0);
		}
		return hString;
		
	}
    	
    	
    	
    	
    	/**
         * add by lsc 2019/3/1
         * Ϊ�˻�ȡ���е�ȫ�ֱ�������Ϣ
         * @return
         */
    	public List<List<String>> getGlobaVariables(List<String> files,HashMap<String, ASTTranslationUnit> astmap) {
    		
    		//��ӡ�﷨��
    		for(String string : files) {
    		
    			ASTTranslationUnit rooTranslationUnit = astmap.get(string);
    			System.err.println(rooTranslationUnit);
    			
    			List<SimpleNode> list =  rooTranslationUnit.findXpath(".//ExternalDeclaration/Declaration");
    			int count = 0;
    			for(SimpleNode astDeclarator: list) {
    				if(count == 0) {
    					count ++;
    					continue;
    				}
    				List<SimpleNode> listTreeNodeList  = astDeclarator.findXpath(".//DirectDeclarator");
    				for(SimpleNode node: listTreeNodeList) {
    					ASTDirectDeclarator astDirectDeclarator =  (ASTDirectDeclarator) node;
    					List<String> list2 = new ArrayList<>();
    					
    					String fileString = string;
    					String varString = astDirectDeclarator.getImage();
    					int row = astDirectDeclarator.getBeginLine();
    					
    					list2.add(fileString);
    					list2.add(varString);
    					list2.add(String.valueOf(row));
    					global_VariablesList.add(list2);
    				}
    				
    			
    				
    			}
    			
    		}
    		System.out.println("ȫ�ֱ�������ϢΪ�� " +global_VariablesList);
    		return global_VariablesList;
    	}
    	
    	private void compareGlobal(){
    		
    		String functionName = "";
    		for(Map<VexNode,String> map:list){
    			for(VexNode node:map.keySet()){
    				String val = map.get(node);
    				boolean flg = false;
    				for(int i=0;i<global_VariablesList.size();i++){
    					if(global_VariablesList.get(i).get(1).equals(val)){
    						flg = true;
    						VexNode nodeTemp = null;
    						if(functionName.equals("")){
    							for(VexNode vexNode : node.getGraph().getAllnodes()) {
        							if(vexNode.getSnumber() == 0) {
        								nodeTemp = vexNode;
        								break;
        							}
        						}
        						
        						functionName =  nodeTemp.getTreenode().getImage();
    						}
    					}
    				}
    				if(!flg){
    					list.remove(map);
    				}
    			}
    		}
    		if(!functionName.equals("")){
    			
    			if(list != null && list.size()!=0){
    				List<Map<VexNode,String>> tem = new LinkedList<Map<VexNode,String>>(list);
    				functionGlobal.put(functionName,tem);
    			}
    			
    		}
    		
    	}
    	
    	
    	 /**
    	  * ��ȡȫ�ֱ���ժҪ���ⲿ����
    	  * @param list_outsource �ⲿ����Դ
    	  * @param files ȫ���ļ� .c
    	  * @param astmap ȫ���﷨�����ļ���ӳ��
    	  * @param list_function ȫ����������
    	  * @param cfgmap ��������ͼ��ӳ��
    	 * @return 
    	  */
        //addbyxlm 20190306\
    	
    	
        
        public HashMap<String, List<Map<VexNode, String>>> getAllGlobalChange(List<String> list_outsource,List<String> files,HashMap<String, ASTTranslationUnit> astmap,List<String> list_function,HashMap<String, Graph> cfgmap ){
        	//��ȡȫ���ⲿ����Դ
    		this.list_outsource = list_outsource;
    		depchainDeadLine depchainD = new depchainDeadLine();
    		try {
    			getGlobaVariables(files, astmap);
    		    //��ȡ����ȫ������
    			List<String> fun= list_function;
    			
    			for(String funName : fun){
    				List<VexNode> vexNodeList = cfgmap.get(funName).getAllnodes();
    				List<List<VexNode>> listtempList = new ArrayList<>();
    				List<List<VexNode>> nodePaths = depchainD.findpathNew(new ArrayList<VexNode>(), vexNodeList.get(vexNodeList.size()-1), listtempList);
    				findFunctionGlobal(nodePaths);
    			}
    			
//    			System.out.println("ȫ����Ϣ��"+functionGlobal);
    		} catch (Exception e) {
    			e.printStackTrace();
    		}
    		return functionGlobal;
    		
        }

		



}
