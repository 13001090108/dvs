package softtest.depchain.c;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.List;

import org.xml.sax.InputSource;

import com.alibaba.fastjson.JSON;
import com.alibaba.fastjson.JSONArray;

import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;
import softtest.cfg.c.VexNode;
import softtest.symboltable.c.NameOccurrence;

public class ExternalInputSourceVisitor implements GraphVisitor {
	private static String[] getInputSourceFromFile() {
    	try {
    		File file = new File("config/inputsource.json");
    		FileReader reader = new FileReader(file);
    		BufferedReader bReader = new BufferedReader(reader);
    		StringBuffer str = new StringBuffer();
    		String s = "";
            while ((s = bReader.readLine()) != null) {//逐行读取文件内容，不读取换行符和末尾的空格
                str.append(s + "\n");//将读取的字符串添加换行符后累加存放在缓存中
            }
    		JSONArray jsonArray = JSON.parseArray(str.toString());
    		String[] ret = new String[jsonArray.size()];
    		for (int i = 0; i < jsonArray.size(); i++) {
    			ret[i] = jsonArray.getString(i);
    		}
    		return ret;
    	} catch (Exception e) {
    		e.printStackTrace();
    	}
    	return null;
	}
	@Override
	public void visit(VexNode n, Object data) {
		// TODO Auto-generated method stub
		List<ExternalInputSource> list = (List<ExternalInputSource>) data;
		for(NameOccurrence occ : n.getOccurrences()) {
	    	SimpleNode astNode = occ.getLocation();
	    	//String[] defFuncs = new String[]{"scanf","gets","strcpy","strdup","free","malloc","calloc","realloc","gets","getc","getchar","fopen"};
	    	String[] defFuncs = ExternalInputSourceVisitor.getInputSourceFromFile();

	    	if (defFuncs == null) {
	    		//如果加载失败，则使用缺省配置
	    		defFuncs = new String[]{"scanf","gets","strcpy","strdup","free","malloc","calloc","realloc","gets","getc","getchar","fopen"};
	    	}
	    	System.out.println("外部输入源：");
	    	for(String def : defFuncs) {
	    		System.out.println(def);
	    	}
	    	if(astNode.containsParentOfType(ASTStatement.class)) {
		    	SimpleNode statementAncestor = (SimpleNode) astNode.getFirstParentOfType(ASTStatement.class);
		    	if(statementAncestor.containsChildOfType(ASTPrimaryExpression.class)) {
		    		SimpleNode primaryNode = (SimpleNode) statementAncestor.getFirstChildOfType(ASTPrimaryExpression.class);
		    		if (((ASTPrimaryExpression)primaryNode).isMethod()) { // 该节点是函数调用
		    			String funcName = primaryNode.getImage();
		    			for(String defFunc:defFuncs) {
			    			if(funcName.equals(defFunc)) {
			    				System.out.println(funcName+"函数是定义点，进行修正！");
			    				ExternalInputSource e = new ExternalInputSource();
			    				e.setFileName(astNode.getFileName());
			    				e.setVarName(occ.getImage());
			    			//	e.setFuncName(n.getGraph().getEntryNode().toString().split("_")[2]);
			    				String temp = n.getGraph().getEntryNode().toString();
			    				
			    				String tempfuncname = temp.split("func_head_")[1].replaceAll("_0", "");
			    				
			    				e.setFuncName(tempfuncname);
			    				
			    				e.setLine(Integer.valueOf(occ.toString().split(":")[1]));
			    				list.add(e);
			    			}
		    			}
		    		}
		    	}
	    	}
	    	if (occ.getSCVP() != null) {
	    		for(String defFunc:defFuncs) {
	    			if (occ.getSCVP().getStructure()!= null) {
		    			if (occ.getSCVP().getStructure().contains(defFunc) || occ.getSCVP().getStructure().contains("Lib")) {
		    				ExternalInputSource e = new ExternalInputSource();
		    				e.setFileName(astNode.getFileName());
		    				e.setVarName(occ.getImage());
		    				String temp = n.getGraph().getEntryNode().toString();
		    				
		    				String tempfuncname = temp.split("func_head_")[1].replaceAll("_0", "");
		    				//System.out.println(tempfuncname);
		    				e.setFuncName(tempfuncname);
		    				e.setLine(Integer.valueOf(occ.toString().split(":")[1]));
		    				list.add(e);
		    			}
	    			}
	    		}
	    	}
	    	
		}
	}

	@Override
	public void visit(Edge e, Object data) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(Graph g, Object data) {
		// TODO Auto-generated method stub

	}

}
