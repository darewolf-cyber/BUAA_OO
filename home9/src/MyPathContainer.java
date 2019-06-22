import com.oocourse.specs1.models.Path;
import com.oocourse.specs1.models.PathContainer;
import com.oocourse.specs1.models.PathIdNotFoundException;
import com.oocourse.specs1.models.PathNotFoundException;

import java.util.HashMap;

public class MyPathContainer implements PathContainer {
    //@ public instance model non_null Path[] pList;
    //@ public instance model non_null int[] pidList;
    private HashMap<Path, Integer> map;
    private HashMap<Integer, Path> idmap;
    private HashMap<Integer,Integer> dismap; //node->num
    private int maxid;

    public MyPathContainer() {
        map = new HashMap<>();
        idmap = new HashMap<>();
        dismap = new HashMap<>();
        maxid = 0;
    }

    @Override
    //@ ensures \result == pList.length;
    public /*@pure@*/int size() {
        return map.size();
    }

    @Override
    /*@ requires path != null;
      @ assignable \nothing;
      @ ensures \result == (\exists int i; 0 <= i && i < pList.length;
      @                     pList[i].equals(path));
      @*/
    public /*@pure@*/ boolean containsPath(Path path) {
        return map.containsKey(path);
    }

    @Override
    /*@ ensures \result == (\exists int i; 0 <= i && i < pidList.length;
      @                      pidList[i] == pathId);
      @*/
    public /*@pure@*/ boolean containsPathId(int pathId) {
        return idmap.containsKey(pathId);
    }

    @Override
    /*@ public normal_behavior
      @ requires containsPathId(pathId);
      @ assignable \nothing;
      @ ensures (pidList.length == pList.length)&&(\exists int i; 0 <= i
      @   && i < pList.length; pidList[i] == pathId && \result == pList[i]);
      @ also
      @ public exceptional_behavior
      @ requires !containsPathId(pathId);
      @ assignable \nothing;
      @ signals_only PathIdNotFoundException;
      @*/
    public /*@pure@*/ Path getPathById(int pathId)
            throws PathIdNotFoundException {
        if (containsPathId(pathId)) {
            return idmap.get(pathId);
        }
        else {
            throw new PathIdNotFoundException(pathId);
        }
    }

    @Override
    /*@ public normal_behavior
      @ requires path != null && path.isValid() && containsPath(path);
      @ assignable \nothing;
      @ ensures (pidList.length == pList.length) && (\exists int i; 0 <= i
      @    && i < pList.length; pList[i].equals(path) && pidList[i] == \result);
      @ also
      @ public exceptional_behavior
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) !path.isValid();
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public /*@pure@*/ int getPathId(Path path) throws PathNotFoundException {
        if (path != null && path.isValid() && containsPath(path)) {
            return map.get(path);
        }
        else {
            throw new PathNotFoundException(path);
        }
    }

    @Override
    /*@ normal_behavior
      @ requires path != null && path.isValid();
      @ assignable pList, pidList;
      @ ensures (pidList.length == pList.length);
      @ ensures (\exists int i; 0 <= i && i < pList.length; pList[i] == path &&
      @           \result == pidList[i]);
      @ ensures !\old(containsPath(path)) ==>
      @          pList.length == (\old(pList.length) + 1) &&
      @          pidList.length == (\old(pidList.length) + 1);
      @ ensures (\forall int i; 0 <= i && i < \old(pList.length);
      @       containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
      @ also
      @ normal_behavior
      @ requires path == null || path.isValid() == false;
      @ assignable \nothing;
      @ ensures \result == 0;
      @*/
    public int addPath(Path path) {
        if (path != null && path.isValid()) {
            if (!containsPath(path)) {
                map.put(path,maxid + 1);
                idmap.put(maxid + 1,path);
                //path加进来 需要修改dismap
                for (Integer id : path) {
                    if (dismap.containsKey(id)) {
                        dismap.put(id,dismap.get(id) + 1);
                    }
                    else {
                        dismap.put(id,1);
                    }
                }
                maxid++;
                return maxid;
            }
            else { //path已经存在
                return map.get(path);
            }
        }
        else {
            return 0;
        }
    }

    @Override
    /*@ public normal_behavior
      @ requires path != null && path.isValid() && \old(containsPath(path));
      @ assignable pList, pidList;
      @ ensures containsPath(path) == false;
      @ ensures (pidList.length == pList.length);
      @ ensures (\exists int i; 0 <= i && i < \old(pList.length);
      @      \old(pList[i].equals(path)) && \result == \old(pidList[i]));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) path.isValid()==false;
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public int removePath(Path path) throws PathNotFoundException {
        if (path != null && path.isValid() && containsPath(path)) {
            int id = map.get(path);
            map.remove(path);
            idmap.remove(id);
            //删除path成功 修改dismap path中的每一节点都应该存在于dismap中的
            for (Integer i : path) {
                if (dismap.get(i) == 1) { //删除就变成0了 直接remove出map
                    dismap.remove(i);
                }
                else {
                    dismap.put(i,dismap.get(i) - 1);
                }
            }
            return id;
        }
        else {
            throw new PathNotFoundException(path);
        }
    }

    @Override
    /*@ public normal_behavior
      @ requires \old(containsPathId(pathId));
      @ assignable pList, pidList;
      @ ensures pList.length == pidList.length;
      @ ensures (\forall int i; 0 <= i && i < pidList.length;
      @               pidList[i] != pathId);
      @ ensures (\forall int i; 0 <= i && i < pList.length;
      @         !pList[i].equals(\old(getPathById(pathId))));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathIdNotFoundException e) !containsPathId(pathId);
      @*/
    public void removePathById(int pathId) throws PathIdNotFoundException {
        if (containsPathId(pathId)) {
            Path path = idmap.get(pathId);
            idmap.remove(pathId);
            map.remove(path);
            for (Integer i : path) {
                if (dismap.get(i) == 1) { //删除就变成0了 直接remove出map
                    dismap.remove(i);
                }
                else {
                    dismap.put(i,dismap.get(i) - 1);
                }
            }
        }
        else {
            throw new PathIdNotFoundException(pathId);
        }
    }

    @Override
    /*@ ensures \result == (\num_of int[] nlist;
           (\forall int i,j; 0 <= i && i < pList.length &&
           0 <= j && j < pList[i].size();
           (\exists int k; 0 <= k && k < nlist.length;
           nlist[k] == pList[i].getNode(j)));
           (\forall int m, n; 0 <= m && m < n && n < nlist.length;
           nlist[m] != nlist[n]));
      @*/
    public /*@pure@*/int getDistinctNodeCount() { //在容器全局范围内查找不同的节点数
        //Set<Integer> set = new HashSet<>();
        //for (Path path : map.keySet()) {
        //    for (Integer i : path) {
        //        set.add(i);
        //    }
        //}
        //return set.size();
        return dismap.size();
    }

}
