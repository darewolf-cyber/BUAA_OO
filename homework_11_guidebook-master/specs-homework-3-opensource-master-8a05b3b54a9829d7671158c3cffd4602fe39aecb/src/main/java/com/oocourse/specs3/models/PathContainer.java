package com.oocourse.specs3.models;

public interface PathContainer {
    //@ public instance model non_null Path[] pList;
    //@ public instance model non_null int[] pidList;
    //@ public invariant pList.length == pidList.length;
    //@ public constraint Math.abs(pList.length - \old(pList.length)) <= 1;


    //@ ensures \result == pList.length;
    public /*@pure@*/int size();

    /*@ requires path != null;
      @ assignable \nothing;
      @ ensures \result == (\exists int i; 0 <= i && i < pList.length;
      @                     pList[i].equals(path));
      @*/
    public /*@pure@*/ boolean containsPath(Path path);

    /*@ ensures \result == (\exists int i; 0 <= i && i < pidList.length;
      @                      pidList[i] == pathId);
      @*/
    public /*@pure@*/ boolean containsPathId(int pathId);

    /*@ public normal_behavior
      @ requires containsPathId(pathId);
      @ assignable \nothing;
      @ ensures (\exists int i; 0 <= i && i < pList.length; pidList[i] == pathId && \result == pList[i]);
      @ also
      @ public exceptional_behavior
      @ requires !containsPathId(pathId);
      @ assignable \nothing;
      @ signals_only PathIdNotFoundException;
      @*/
    public /*@pure@*/ Path getPathById(int pathId) throws PathIdNotFoundException;

    /*@ public normal_behavior
      @ requires path != null && path.isValid() && containsPath(path);
      @ assignable \nothing;
      @ ensures (\exists int i; 0 <= i && i < pList.length; pList[i].equals(path) && pidList[i] == \result);
      @ also
      @ public exceptional_behavior
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) !path.isValid();
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public /*@pure@*/ int getPathId(Path path) throws PathNotFoundException;

    /*@ normal_behavior
      @ requires path != null && path.isValid();
      @ assignable pList, pidList;
      @ ensures (\exists int i; 0 <= i && i < pList.length; pList[i] == path &&
      @           \result == pidList[i]);
      @ ensures (\forall int i; 0 <= i && i < \old(pList.length);
      @          containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
      @ also
      @ normal_behavior
      @ requires path == null || path.isValid() == false;
      @ assignable \nothing;
      @ ensures \result == 0;
      @*/
    public int addPath(Path path);

    /*@ public normal_behavior
      @ requires path != null && path.isValid() && containsPath(path);
      @ assignable pList, pidList;
      @ ensures containsPath(path) == false;
      @ ensures (\exists int i; 0 <= i && i < \old(pList.length); \old(pList[i].equals(path)) &&
      @           \result == \old(pidList[i]));
      @ ensures (\forall int i; 0 <= i && i < \old(pList.length) && \old(pList[i].equals(path) == false);
      @          containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) path.isValid() == false;
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public int removePath(Path path) throws PathNotFoundException;

    /*@ public normal_behavior
      @ requires containsPathId(pathId);
      @ assignable pList, pidList;
      @ ensures (\forall int i; 0 <= i && i < pidList.length; pidList[i] != pathId);
      @ ensures (\forall int i; 0 <= i && i < pList.length; !pList[i].equals(\old(getPathById(pathId))));
      @ ensures (\forall int i; 0 <= i && i < \old(pidList.length) && pidList[i] != pathId;
      @         containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathIdNotFoundException e) !containsPathId(pathId);
      @*/
    public void removePathById(int pathId) throws PathIdNotFoundException;

    /*@ ensures (\exists int[] arr; (\forall int i, j; 0 <= i && i < j && j < arr.length; arr[i] != arr[j]);
	  @            (\forall int i; 0 <= i && i < arr.length; (\exists Path p; this.containsPath(p); p.containsNode(arr[i])))
	  @            &&(\forall Path p; this.containsPath(p); (\forall int node; p.containsNode(node); (\exists int i; 0 <= i && i < arr.length; node == arr[i])))
	  @            &&(\result == arr.length));
	  @*/
    public /*@pure@*/int getDistinctNodeCount(); //在容器全局范围内查找不同的节点数
}