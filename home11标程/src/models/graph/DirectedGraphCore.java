package models.graph;

import models.base.Edge;

public class DirectedGraphCore extends GraphCore {
    public DirectedGraphCore() {
        super();
    }

    public void addDoubleEdge(Edge edge, int weight) {
        this.addEdge(edge, weight);
        this.addEdge(edge.getReversedEdge(), weight);
    }

    public void removeDoubleEdge(Edge edge) {
        this.removeEdge(edge);
        this.removeEdge(edge.getReversedEdge());
    }
}
