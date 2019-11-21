package com.oocourse.specs3.models;

/**
 * 地铁系统
 */
public interface RailwaySystem extends Graph {
    /*@ normal_behavior
      @ requires containsNode(fromNodeId) && containsNode(toNodeId) && isConnected(fromNodeId, toNodeId);
      @ assignable \nothing;
      @ ensures (\exists Path[] tpath; isConnectedInPathSequence(tpath, fromNodeId, toNodeId);
      @              \result == getTicketPrice(tpath, fromNodeId, toNodeId) &&
      @            (\forall Path[] spath; isConnectedInPathSequence(spath, fromNodeId, toNodeId); \result <= getTicketPrice(spath, fromNodeId, toNodeId)));
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e) !containsNode(fromNodeId); 
      @ signals (NodeIdNotFoundException e) !containsNode(toNodeId);
      @ signals (NodeNotConnectedException e) !isConnected(fromNodeId, toNodeId);
      @*/
    public int getLeastTicketPrice(int fromNodeId, int toNodeId) throws NodeIdNotFoundException, NodeNotConnectedException;

    /*@ normal_behavior
      @ requires containsNode(fromNodeId) && containsNode(toNodeId) && isConnected(fromNodeId,toNodeId);
      @ ensures (\exists Path[] tpath; isConnectedInPathSequence(tpath, fromNodeId, toNodeId);
      @         (\forall Path[] spath; isConnectedInPathSequence(spath, fromNodeId, toNodeId); tpath.length <= spath.length) &&
      @           \result == tpath.length - 1);
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e) !containsNode(fromNodeId); 
      @ signals (NodeIdNotFoundException e) !containsNode(toNodeId);
      @ signals (NodeNotConnectedException e) !isConnected(fromNodeId, toNodeId);
      @*/
    public int getLeastTransferCount(int fromNodeId, int toNodeId) throws NodeIdNotFoundException, NodeNotConnectedException;

    /*@ normal_behavior
      @ requires containsNode(fromNodeId) && containsNode(toNodeId) && isConnected(fromNodeId,toNodeId);
      @ ensures (\exists Path[] tpath; isConnectedInPathSequence(tpath, fromNodeId, toNodeId); \result == getUnpleasantValue(tpath, fromNodeId, toNodeId) &&
      @         (\forall Path[] spath; isConnectedInPathSequence(tpath, fromNodeId, toNodeId); getUnpleasantValue(spath, fromNodeId, toNodeId) >= \result));
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e) !containsNode(fromNodeId); 
      @ signals (NodeIdNotFoundException e) !containsNode(toNodeId);
      @ signals (NodeNotConnectedException e) !isConnected(fromNodeId, toNodeId);
      @*/
    public int getLeastUnpleasantValue(int fromNodeId, int toNodeId) throws NodeIdNotFoundException, NodeNotConnectedException;

    /*@ ensures (\exists int[\result][] blocks; (\forall int i, j; 0 <= i && i< \result && 0 <= j && j < blocks[i].length; containsNode(blocks[i][j]));
      @          (\forall int i; 0 <= i && i < \result; (\forall int j, k; 0 <= j && j < k && k < blocks[i].length; blocks[i][j] != blocks[i][k] && isConnected(blocks[i][j], blocks[i][k]))) &&
      @          (\forall int i, j; 0 <= i && i < j && j < \result; !(\exists int k,m; 0 <= k && k < blocks[i].length && 0 <= m && m < blocks[j].length; isConnected(blocks[i][k], blocks[j][m])))&&
      @          (\sum int i; 0 <= i && i < \result; blocks[i].length) == getDistinctNodeCount());
      @*/
    public int getConnectedBlockCount();

    //@ensures \result == (pseq != null) && (\forall int i; 0 <= i && i < pseq.length; containsPath(pseq[i]));
    //It is not required to implement this interface, just for constructing the JML spec.
    public /*@pure@*/ boolean containsPathSequence(Path[] pseq);

    /*@ normal_behavior
      @ requires containsNode(fromNodeId) && containsNode(toNodeId) && containsPathSequence(pseq);
      @ ensures \result == (\exists int[] tn_idx; tn_idx.length == pseq.length * 2; pseq[0].getNode(tn_idx[0]) == fromNodeId &&
      @             pseq[pseq.length - 1].getNode(tn_idx[tn_idx.length - 1]) == toNodeId &&
      @            (\forall int i; 0 <= i && i < pseq.length - 1; pseq[i].getNode(tn_idx[2 * i + 1]) == pseq[i + 1].getNode(tn_idx[2 * i + 2])));
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e) !containsNode(fromNodeId) || !containsNode(toNodeId);
      @ signals (PathNotFoundException e) pseq == null || (\exists int i; 0 <= i && i < pseq.length; !containsPath(pseq[i]));
      @*/
    //It is not required to implement this interface, just for constructing the JML spec.
    public /*@pure@*/ boolean isConnectedInPathSequence(Path[] pseq, int fromNodeId, int toNodeId) throws NodeIdNotFoundException, PathNotFoundException;

    /*@ requires containsNode(fromNodeId) && containsNode(toNodeId) && containsPathSequence(pseq);
      @ ensures (\exists int[] tn_idx; tn_idx.length == pseq.length * 2; pseq[0].getNode(tn_idx[0]) == fromNodeId &&
      @             pseq[pseq.length - 1].getNode(tn_idx[tn_idx.length - 1]) == toNodeId &&
      @            (\forall int i; 0 <= i && i < pseq.length - 1; pseq[i].getNode(tn_idx[2 * i + 1]) == pseq[i + 1].getNode(tn_idx[2 * i + 2])) &&
      @             \result == (\sum int j; 0 <= j && j < pseq.length; getShortestPathLength(pseq[j].getNode(tn_idx[2 * j + 1]), pseq[j].getNode(tn_idx[2 * j]))) + (pseq.length - 1) * 2);
      @*/
    //It is not required to implement this interface, just for constructing the JML spec.
    public /*@pure@*/ int getTicketPrice(Path[] pseq, int fromNodeId, int toNodeId);

    /*@ ensures (path != null && idx != null && (\forall int i; 0 <= i && i < idx.length; 0 <= idx[i] && idx[i] < path.size())) ==>
      @     \result == (\sum int i; 0 <= i && i < idx.length - 1; (\max int x; 0 <= x && x < 2; path.getUnpleasantValue(path.getNode(idx[i] + x))));
      @ ensures (path == null) || (idx == null) ==> \result == 0;
      @ ensures (path != null && idx != null && (\exists int i; 0 <= i && i < idx.length; 0 > idx[i] || idx[i] >= path.size())) ==> \result == 0;
      @*/
    //It is not required to implement this interface, just for constructing the JML spec.
    public /*@pure@*/ int getUnpleasantValue(Path path, int[] idx);

    /*@ requires containsPath(path) && 0 <= fromIndex && fromIndex < toIndex && toIndex < path.size();
      @ ensures (\exists int[] mred; mred[0] == fromIndex && mred[mred.length - 1] == toIndex && mred.length <= (toIndex - fromIndex) && (\forall int i; 0 <= i && i < mred.length - 1; path.containsEdge(path.getNode(mred[i]), path.getNode(mred[i + 1])));
      @           (\forall int[] red; red[0] == fromIndex && red[red.length - 1] == toIndex && red.length <= (toIndex - fromIndex) && (\forall int i; 0 <= i && i < red.length - 1; path.containsEdge(path.getNode(red[i]), path.getNode(red[i + 1]))) &&
      @                       getUnpleasantValue(path, mred) <= getUnpleasantValue(path, red)) && \result == getUnpleasantValue(path, mred));
      @*/
    public /*@pure@*/ int getUnpleasantValue(Path path, int fromIndex, int toIndex);

    /*@ requires containsNode(fromNodeId) && containsNode(toNodeId) && containsPathSequence(pseq);
      @ ensures (\exists int[] tn_idx; tn_idx.length == pseq.length * 2; pseq[0].getNode(tn_idx[0]) == fromNodeId &&
      @             pseq[pseq.length - 1].getNode(tn_idx[tn_idx.length - 1]) == toNodeId &&
      @            (\forall int i; 0 <= i && i < pseq.length - 1; pseq[i].getNode(tn_idx[2 * i + 1]) == pseq[i + 1].getNode(tn_idx[2 * i + 2])) &&
      @             \result == (\sum int j; 0 <= j && j < pseq.length; getUnpleasantValue(pseq[j], tn_idx[2 * j], tn_idx[2 * j + 1])) + 32 * (pseq.length - 1));
      @*/
    //It is not required to implement this interface, just for constructing the JML spec.
    public /*@pure@*/ int getUnpleasantValue(Path[] pseq, int fromNodeId, int toNodeId);
}    