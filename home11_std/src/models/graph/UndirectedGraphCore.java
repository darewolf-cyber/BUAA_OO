package models.graph;

import models.base.Edge;

public class UndirectedGraphCore extends GraphCore {
    public UndirectedGraphCore() {
        super();
    }

    public void addEdge(Edge edge, int weight) {
        super.addEdge(edge, weight);
        super.addEdge(edge.getReversedEdge(), weight);
    }

    public void removeEdge(Edge edge) {
        super.removeEdge(edge);
        super.removeEdge(edge.getReversedEdge());
    }
}
