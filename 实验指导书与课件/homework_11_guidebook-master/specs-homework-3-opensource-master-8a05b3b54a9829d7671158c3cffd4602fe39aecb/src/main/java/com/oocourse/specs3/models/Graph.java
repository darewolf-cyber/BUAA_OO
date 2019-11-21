package com.oocourse.specs3.models;

/**
 * 图类
 */
public interface Graph extends PathContainer {
    //@ ensures \result == (\exists Path path; path.isValid() && containsPath(path); path.containsNode(nodeId));
    public /*@pure@*/ boolean containsNode(int nodeId);

    /*@ ensures \result == (\exists Path path; path.isValid() && containsPath(path);
      @      (\exists int i; 0 <= i && i < path.size() - 1; (path.getNode(i) == fromNodeId && path.getNode(i + 1) == toNodeId) ||
      @        (path.getNode(i) == toNodeId && path.getNode(i + 1) == fromNodeId)));
      @*/
    public /*@pure@*/ boolean containsEdge(int fromNodeId, int toNodeId);

    /*@ normal_behavior
      @ requires (\exists Path path; path.isValid() && containsPath(path); path.containsNode(fromNodeId)) &&
      @          (\exists Path path; path.isValid() && containsPath(path); path.containsNode(toNodeId));
      @ assignable \nothing;
      @ ensures (fromNodeId != toNodeId) ==> \result == (\exists int[] npath; npath.length >= 2 && npath[0] == fromNodeId && npath[npath.length - 1] == toNodeId;
      @                     (\forall int i; 0 <= i && (i < npath.length - 1); containsEdge(npath[i], npath[i + 1])));
      @ ensures (fromNodeId == toNodeId) ==> \result == true;
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e) (\forall Path path; containsPath(path); !path.containsNode(fromNodeId)); 
      @ signals (NodeIdNotFoundException e) (\forall Path path; containsPath(path); !path.containsNode(toNodeId));
      @*/
    public /*@pure@*/ boolean isConnected(int fromNodeId, int toNodeId) throws NodeIdNotFoundException;

    /*@ normal_behavior
      @ requires (\exists Path path; path.isValid() && containsPath(path); path.containsNode(fromNodeId)) &&
      @          (\exists Path path; path.isValid() && containsPath(path); path.containsNode(toNodeId));
      @ assignable \nothing;
      @ ensures (fromNodeId != toNodeId) ==> (\exists int[] spath; spath.length >= 2 && spath[0] == fromNodeId && spath[spath.length - 1] == toNodeId;
      @             (\forall int i; 0 <= i && (i < spath.length - 1); containsEdge(spath[i], spath[i + 1])) &&
      @             (\forall Path p; p.isValid() && p.getNode(0) == fromNodeId && p.getNode(p.size() - 1) == toNodeId && 
      @               (\forall int i; 0 <= i && (i < p.size() - 1); containsEdge(p.getNode(i), p.getNode(i + 1))); p.size() >= spath.length) &&
      @             (\result == spath.length - 1));
      @ ensures (fromNodeId == toNodeId) ==> \result == 0;
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e) (\forall Path path; containsPath(path); !path.containsNode(fromNodeId)); 
      @ signals (NodeIdNotFoundException e) (\forall Path path; containsPath(path); !path.containsNode(toNodeId));
      @ signals (NodeNotConnectedException e) !(\exists int[] npath; npath.length >= 2 && npath[0] == fromNodeId && npath[npath.length - 1] == toNodeId;
      @                                          (\forall int i; 0 <= i && (i < npath.length - 1); containsEdge(npath[i], npath[i + 1])));
      @*/
    public /*@pure@*/ int getShortestPathLength(int fromNodeId, int toNodeId) throws NodeIdNotFoundException, NodeNotConnectedException;
}
