package softtest.depchain.c;




import java.util.ArrayList;
import java.util.List;

import com.alibaba.fastjson.JSONArray;
import com.alibaba.fastjson.JSONObject;

import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;
import softtest.cfg.c.VexNode;
import softtest.scvp.c.SCVPString;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;

public class DepChainUtil {
	/**
	 * 
	 * @param g
	 * @param funcName
	 * @return
	 */
	public static List<VexNode> findCallVexodes(Graph g,String funcName) {
		List<VexNode> callNodes = new ArrayList<>();
		VexNode entNode = g.getEntryNode();
		SimpleNode entTreeNode = entNode.getTreenode();
		List<Node> leaves = entTreeNode.findLeafChildrenOfType(ASTPrimaryExpression.class);
		for(Node n : leaves) {
			if(n instanceof ASTPrimaryExpression) {
				if(((ASTPrimaryExpression)n).isMethod()) {
					String methodName = ((ASTPrimaryExpression) n).getImage();
					if(methodName.equals(funcName)) {
						callNodes.add((((ASTPrimaryExpression) n).getCurrentVexNode()));
					}
				}
			}
		}
		return callNodes;
	}

	public static List<NameOccurrence> findCondition(VexNode n) {
		List<NameOccurrence> occs = new ArrayList<>();
		
		List<VexNode> path = Graph.findAPath(n.getGraph().getEntryNode(), n);
		for(VexNode node : path) {
			if(node.getName().contains("if_head")) {
				occs.addAll(node.getOccurrences());
			}
		}
		return occs;
	}
	
	public static class listSCVPVisitor implements GraphVisitor {

		@Override
		public void visit(VexNode n, Object data) {
			// TODO Auto-generated method stub
			JSONObject jsonObject = (JSONObject) data;
			JSONArray occArray = new JSONArray();
			for(NameOccurrence occ : n.getOccurrences()) {
				JSONObject occObj = new JSONObject(true);
				occObj.put("name", occ.toString());
				occObj.put("Type", occ.getOccurrenceType().toString());
				if(occ.getOccurrenceType() == OccurrenceType.DEF) {
					JSONObject scvpObj = new JSONObject(true);
					SCVPString scvp = occ.getSCVP();
					scvpObj.put("S", scvp.getStructure());
					scvpObj.put("C", scvp.getConstants().toString());
					scvpObj.put("V", scvp.getOccs().toString());
					scvpObj.put("P", scvp.getPosition().toString());
					occObj.put("SCVP", scvpObj);
				}
				
				JSONArray usedefArray = new JSONArray();
				if(occ!=null && occ.getUse_def()!=null) {
					for(NameOccurrence usedefOcc:occ.getUse_def()) {
						usedefArray.add(usedefOcc.toString());
					}
					if(usedefArray.size()!=0)
						occObj.put("usedef", usedefArray);
				}
				
				if(occ!=null && occ.getDef_use()!=null) {
					JSONArray defuseArray = new JSONArray();
					for(NameOccurrence defuseOcc:occ.getDef_use()) {
						defuseArray.add(defuseOcc.toString());
					}
					if(defuseArray.size()!=0)
						occObj.put("defuse", defuseArray);
				}
				occArray.add(occObj);
			}
			jsonObject.put(n.getName(), occArray);			
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
}
