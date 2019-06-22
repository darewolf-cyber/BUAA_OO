package com.oocourse.specs1.models;

public interface Path extends Iterable<Integer>, Comparable<Path> {
    // Iterable<Integer>和Comparable<Path>接口的规格请参阅JDK
    //@ public instance model non_null int[] nodes;

    //@ ensures \result == nodes.length;
    public /*@pure@*/int size();

    /*@ requires index >= 0 && index < size();
      @ assignable \nothing;
      @ ensures \result == nodes[index];
      @*/
    public /*@pure@*/ int getNode(int index);

    //@ ensures \result == (\exists int i; 0 <= i && i < nodes.length; nodes[i] == node);
    public /*@pure@*/ boolean containsNode(int node);

    /*@ ensures \result == (\num_of int i, j; 0 <= i && i < j && j < nodes.length;
                             nodes[i] != nodes[j]);
      @*/
    public /*pure*/ int getDistinctNodeCount();

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Path;
      @ assignable \nothing;
      @ ensures \result == ((Path) obj).nodes.length == nodes.length) &&
      @                      (\forall int i; 0 <= i && i < nodes.length; nodes[i] == ((Path) obj).nodes[i]);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Path);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public boolean equals(Object obj);

    //@ ensures \result == (nodes.length >= 2);
    public /*@pure@*/ boolean isValid();
}