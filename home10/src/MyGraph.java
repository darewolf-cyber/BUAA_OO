import com.oocourse.specs2.models.Graph;
import com.oocourse.specs2.models.NodeIdNotFoundException;
import com.oocourse.specs2.models.NodeNotConnectedException;
import com.oocourse.specs2.models.Path;
import com.oocourse.specs2.models.PathIdNotFoundException;
import com.oocourse.specs2.models.PathNotFoundException;

import java.util.HashMap;
import java.util.LinkedList;

public class MyGraph implements Graph {
    //@ public instance model non_null Path[] pList;
    //@ public instance model non_null int[] pidList;
    //@ public invariant pList.length == pidList.length;
    //@ public constraint Math.abs(pList.length - \old(pList.length)) <= 1;
    private HashMap<Path, Integer> map;
    private HashMap<Integer, Path> idmap;
    private HashMap<Integer,Integer> dismap; //node->num
    private HashMap<Integer, HashMap<Integer,Integer>> lgraph; //from-><to,num>
    private HashMap<Integer, HashMap<Integer,Integer>> dist; //from-><to,dist>
    private int maxid;
    private boolean isDestroy;

    public MyGraph() {
        map = new HashMap<>();
        idmap = new HashMap<>();
        dismap = new HashMap<>();
        lgraph = new HashMap<>();
        dist = new HashMap<>();
        maxid = 0;
        isDestroy = false;
    }

    //@ ensures \result == (\exists Path path; path.isValid()
    //@ && containsPath(path); path.containsNode(nodeId));
    public /*@pure@*/ boolean containsNode(int nodeId) {
        return lgraph.containsKey(nodeId);
    }

    /*@ ensures \result == (\exists Path path; path.isValid()
      @   && containsPath(path);
      @      (\exists int i; 0 <= i && i < path.size() - 1;
      @  (path.getNode(i) == fromNodeId && path.getNode(i + 1) == toNodeId)||
      @    (path.getNode(i) == toNodeId && path.getNode(i + 1) == fromNodeId)));
      @*/
    public /*@pure@*/ boolean containsEdge(int fromNodeId, int toNodeId) {
        return ((lgraph.containsKey(fromNodeId) &&
                lgraph.get(fromNodeId).containsKey(toNodeId)) ||
                (lgraph.containsKey(toNodeId) &&
                        lgraph.get(toNodeId).containsKey(fromNodeId)));
    }

    /*@ normal_behavior
      @ requires (\exists Path path; path.isValid() && containsPath(path);
      @   path.containsNode(fromNodeId)) &&
      @          (\exists Path path; path.isValid() &&
      @  containsPath(path); path.containsNode(toNodeId));
      @ assignable \nothing;
      @ ensures (fromNodeId != toNodeId) ==> \result == (\exists int[] npath;
      @   npath.length >= 2 && npath[0] == fromNodeId &&
      @   npath[npath.length - 1] == toNodeId;
      @                     (\forall int i; 0 <= i && (i < npath.length - 1);
      @  containsEdge(npath[i], npath[i + 1])));
      @ ensures (fromNodeId == toNodeId) ==> \result == true;
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e) (\forall Path path;
      @ containsPath(path); !path.containsNode(fromNodeId));
      @ signals (NodeIdNotFoundException e) (\forall Path path;
      @ containsPath(path); !path.containsNode(toNodeId));
      @*/
    public boolean isConnected(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException {
        if (!containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        }
        else if (!containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        }
        else {
            if (isDestroy) {
                unWeightedDist();
                isDestroy = false;
            }
            if (fromNodeId == toNodeId) {
                return true;
            }
            if ((dist.containsKey(fromNodeId) &&
                    dist.get(fromNodeId).containsKey(toNodeId)) ||
                    (dist.containsKey(toNodeId) &&
                            dist.get(toNodeId).containsKey(fromNodeId))) {
                return true;
            }
            else {
                return false;
            }
        }
    }

    /*@ normal_behavior
      @ requires (\exists Path path; path.isValid() && containsPath(path);
      @ path.containsNode(fromNodeId)) &&
      @          (\exists Path path; path.isValid() && containsPath(path);
      @ path.containsNode(toNodeId));
      @ assignable \nothing;
      @ ensures (fromNodeId != toNodeId) ==> (\exists int[] spath;
      @ spath.length >= 2 && spath[0] == fromNodeId &&
      @ spath[spath.length - 1] == toNodeId;
      @             (\forall int i; 0 <= i && (i < spath.length - 1);
      @ containsEdge(spath[i], spath[i + 1])) &&
      @             (\forall Path p; p.isValid() && p.getNode(0) == fromNodeId
      @ && p.getNode(p.size() - 1) == toNodeId; p.size() >= spath.length) &&
      @             (\result == spath.length - 1));
      @ ensures (fromNodeId == toNodeId) ==> \result == 0;
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e)
      @(\forall Path path; containsPath(path); !path.containsNode(fromNodeId));
      @ signals (NodeIdNotFoundException e)
      @(\forall Path path; containsPath(path); !path.containsNode(toNodeId));
      @ signals (NodeNotConnectedException e)
      @ !(\exists int[] npath; npath.length >= 2 && npath[0] == fromNodeId
      @   && npath[npath.length - 1] == toNodeId;
      @  (\forall int i; 0 <= i && (i < npath.length - 1);
      @ containsEdge(npath[i], npath[i + 1])));
      @*/
    public int getShortestPathLength(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        }
        else if (!containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        }
        else {
            if (isDestroy) {
                unWeightedDist();
                isDestroy = false;
            }
            if (fromNodeId == toNodeId) {
                return 0;
            }
            if (dist.containsKey(fromNodeId) &&
                    dist.get(fromNodeId).containsKey(toNodeId)) {
                return dist.get(fromNodeId).get(toNodeId);
            }
            else if (dist.containsKey(toNodeId) &&
                    dist.get(toNodeId).containsKey(fromNodeId)) {
                return dist.get(toNodeId).get(fromNodeId);
            }
            else {
                throw new NodeNotConnectedException(fromNodeId,toNodeId);
            }
        }
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
      @ ensures (\exists int i; 0 <= i && i < pList.length;
      @ pidList[i] == pathId && \result == pList[i]);
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
      @ ensures (\exists int i; 0 <= i && i < pList.length;
      @ pList[i].equals(path) && pidList[i] == \result);
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

    private void unWeightedDist() {
        //System.err.println("jisuan !!!!!!!!!!!");
        for (int v : lgraph.keySet()) {
            // 初始化
            HashMap<Integer, Integer> dm = new HashMap<>(); //dist.get(v);
            for (int to : lgraph.keySet()) {
                if (to == v) {
                    dm.put(to, 0);
                }
                else {
                    dm.put(to, -1);
                }
            }
            int num = lgraph.keySet().size();
            LinkedList<Integer> queue = new LinkedList<>();
            queue.addLast(v);
            int i = 1;
            HashMap<Integer, Integer> distm = new HashMap<>();
            distm.put(v,0);
            while (!queue.isEmpty()) {
                int tmp = queue.removeFirst();
                HashMap<Integer, Integer> hm = lgraph.get(tmp); //找邻接点
                for (int to : hm.keySet()) {
                    if (dm.get(to) == -1) {
                        dm.put(to,dm.get(tmp) + 1);
                        distm.put(to, dm.get(tmp) + 1);
                        queue.addLast(to);
                        i++;
                    }
                }
                if (i == num) {
                    break;
                }
            }
            dist.put(v,distm);
            //System.err.println(dist);
        }
    }

    private void add(int from, int to) {
        if (lgraph.containsKey(from)) {
            HashMap<Integer, Integer> hm = lgraph.get(from);
            if (hm.containsKey(to)) {
                hm.put(to,hm.get(to) + 1); //加入重边 没有破坏图
            }
            else {
                hm.put(to,1);
                isDestroy = true; //加入了新的边 破坏了图
            }
        }
        else {
            HashMap<Integer, Integer> hm = new HashMap<>();
            hm.put(to,1);
            lgraph.put(from,hm);
            isDestroy = true; //加入了新的边 破坏了图
        }
    }

    @Override
    /*@ normal_behavior
      @ requires path != null && path.isValid();
      @ assignable pList, pidList;
      @ ensures (\exists int i; 0 <= i && i < pList.length; pList[i] == path &&
      @           \result == pidList[i]);
      @ ensures (\forall int i; 0 <= i && i < \old(pList.length);
      @      containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
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
                for (Integer id : path) {
                    if (dismap.containsKey(id)) {
                        dismap.put(id,dismap.get(id) + 1);
                    }
                    else {
                        dismap.put(id,1);
                        isDestroy = true; //加入了新的点 破坏了图
                    }
                }
                for (int i = 0;i < path.size() - 1; i++) {
                    int from = path.getNode(i);
                    int to = path.getNode(i + 1);
                    add(from,to);
                    add(to,from);
                }
                maxid++;
                //isDestroy = true; 进一步优化 只有破坏图的add才true
                return maxid;
            }
            else {
                return map.get(path);
            }
        }
        else {
            return 0;
        }
    }

    private void remove(int from,int to) {
        HashMap<Integer, Integer> hm = lgraph.get(from);
        if (hm.get(to) == 1) {
            hm.remove(to);
            isDestroy = true; //删除了边 破坏了图
        }
        else {
            hm.put(to,hm.get(to) - 1); //只是减少了重边 没有破坏图
        }
        if (hm.size() == 0) {
            lgraph.remove(from);
            dist.remove(from);
            isDestroy = true; //删除了边 破坏了图
        }
    }

    private void mapRemove(int id,Path path) {
        map.remove(path);
        idmap.remove(id);
        for (Integer i : path) {
            if (dismap.get(i) == 1) {
                dismap.remove(i);
                isDestroy = true; //删除了某个点 破坏了图
            }
            else {
                dismap.put(i,dismap.get(i) - 1);
            }
        }
        for (int i = 0;i < path.size() - 1; i++) {
            int from = path.getNode(i);
            int to = path.getNode(i + 1);
            remove(from,to);
            remove(to,from);
        }
    }

    @Override
    /*@ public normal_behavior
      @ requires path != null && path.isValid() && containsPath(path);
      @ assignable pList, pidList;
      @ ensures containsPath(path) == false;
      @ ensures (\exists int i; 0 <= i && i < \old(pList.length);
      @ \old(pList[i].equals(path)) &&
      @           \result == \old(pidList[i]));
      @ ensures (\forall int i; 0 <= i && i < \old(pList.length)
      @  && \old(pList[i].equals(path) == false);
      @     containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) path.isValid() == false;
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public int removePath(Path path) throws PathNotFoundException {
        if (path != null && path.isValid() && containsPath(path)) {
            int id = map.get(path);
            mapRemove(id,path);
            //isDestroy = true; 进一步优化 只有破坏图的remove才true
            return id;
        }
        else {
            throw new PathNotFoundException(path);
        }
    }

    @Override
    /*@ public normal_behavior
      @ requires containsPathId(pathId);
      @ assignable pList, pidList;
      @ ensures (\forall int i; 0 <= i && i < pidList.length;
      @   pidList[i] != pathId);
      @ ensures (\forall int i; 0 <= i && i < pList.length;
      @     !pList[i].equals(\old(getPathById(pathId))));
      @ ensures (\forall int i; 0 <= i && i < \old(pidList.length)
      @          && pidList[i] != pathId;
      @      containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathIdNotFoundException e) !containsPathId(pathId);
      @*/
    public void removePathById(int pathId) throws PathIdNotFoundException {
        if (containsPathId(pathId)) {
            Path path = idmap.get(pathId);
            mapRemove(pathId,path);
            //isDestroy = true; 进一步优化 只有破坏图的remove才true
        }
        else {
            throw new PathIdNotFoundException(pathId);
        }
    }

    @Override
    /*@ ensures (\exists int[] arr; (\forall int i, j; 0 <= i &&
      @     i < j && j < arr.length; arr[i] != arr[j]);
      @         (\forall int i; 0 <= i && i < arr.length;
      @         (\exists Path p; this.containsPath(p); p.containsNode(arr[i])))
      @         &&(\forall Path p; this.containsPath(p);
      @      (\forall int node; p.containsNode(node);
      @      (\exists int i; 0 <= i && i < arr.length; node == arr[i])))
      @         &&(\result == arr.length));
      @*/
    public /*@pure@*/int getDistinctNodeCount() { //在容器全局范围内查找不同的节点数
        return dismap.size();
    }

}
