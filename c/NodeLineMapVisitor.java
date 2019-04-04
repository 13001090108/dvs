package softtest.depchain.c;

import java.util.HashMap;
import java.util.Map;

import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;
import softtest.cfg.c.VexNode;

public class NodeLineMapVisitor implements GraphVisitor {

	@Override
	public void visit(VexNode n, Object data) {
		// TODO Auto-generated method stub
		Map<String, Integer> nodelineMap =(Map<String, Integer>) data;
		String key = n.getName();
		int value = n.getTreenode().getBeginLine();
		nodelineMap.put(key, value);
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
