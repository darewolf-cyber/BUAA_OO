import com.oocourse.specs3.models.NodeIdNotFoundException;
import com.oocourse.specs3.models.NodeNotConnectedException;
import com.oocourse.specs3.models.Path;
import com.oocourse.specs3.models.PathIdNotFoundException;
import com.oocourse.specs3.models.PathNotFoundException;
import com.oocourse.specs3.models.RailwaySystem;
import javafx.util.Pair;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.PriorityQueue;

public class MyRailwaySystem implements RailwaySystem {
    private HashMap<Path, Integer> map = new HashMap<>();
    private HashMap<Integer, Path> idmap = new HashMap<>();
    private HashMap<Integer,Integer> dismap = new HashMap<>();
    private HashMap<Integer, HashMap<Integer,Integer>> lgraph = new HashMap<>();
    private HashMap<Integer, HashMap<Integer,Integer>> dist = new HashMap<>();
    private HashMap<Pair<Integer,Integer>,HashSet<Pair<Integer,Integer>>>
            graph = new HashMap<>();
    private HashMap<Integer,HashMap<Integer,Integer>> traDist = new HashMap<>();
    private HashMap<Integer,HashMap<Integer,Integer>> priDist = new HashMap<>();
    private HashMap<Integer,HashMap<Integer,Integer>> pleDist = new HashMap<>();
    private HashMap<Integer,Integer> vis = new HashMap<>();
    private int maxid = 0;
    private int blockCnt = 0;
    private boolean isDestroy = false;
    private boolean blockDestroy = false;

    public MyRailwaySystem() { }

    public /*@pure@*/ boolean containsNode(int nodeId) {
        return lgraph.containsKey(nodeId); }

    public /*@pure@*/ boolean containsEdge(int fromNodeId, int toNodeId) {
        return ((lgraph.containsKey(fromNodeId) &&
                lgraph.get(fromNodeId).containsKey(toNodeId)) ||
                (lgraph.containsKey(toNodeId) &&
                        lgraph.get(toNodeId).containsKey(fromNodeId))); }

    public boolean isConnected(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException {
        if (!containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        } else if (!containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        } else {
            if (isDestroy) {
                unWeightedDist();
                isDestroy = false;
            }
            if (fromNodeId == toNodeId) { return true; }
            return ((dist.containsKey(fromNodeId) &&
                    dist.get(fromNodeId).containsKey(toNodeId)) ||
                    (dist.containsKey(toNodeId) &&
                            dist.get(toNodeId).containsKey(fromNodeId)));
        }
    }

    public int getShortestPathLength(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        } else if (!containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        } else {
            if (isDestroy) {
                unWeightedDist();
                isDestroy = false;
            }
            if (fromNodeId == toNodeId) { return 0; }
            if (dist.containsKey(fromNodeId) &&
                    dist.get(fromNodeId).containsKey(toNodeId)) {
                return dist.get(fromNodeId).get(toNodeId);
            } else if (dist.containsKey(toNodeId) &&
                    dist.get(toNodeId).containsKey(fromNodeId)) {
                return dist.get(toNodeId).get(fromNodeId);
            } else { throw new NodeNotConnectedException(fromNodeId,toNodeId); }
        }
    }

    @Override
    public /*@pure@*/int size() { return map.size(); }

    @Override
    public /*@pure@*/ boolean containsPath(Path path) {
        return map.containsKey(path); }

    @Override
    public /*@pure@*/ boolean containsPathId(int pathId) {
        return idmap.containsKey(pathId); }

    @Override
    public /*@pure@*/ Path getPathById(int pathId)
            throws PathIdNotFoundException {
        if (containsPathId(pathId)) { return idmap.get(pathId); }
        else { throw new PathIdNotFoundException(pathId); }
    }

    @Override
    public /*@pure@*/ int getPathId(Path path) throws PathNotFoundException {
        if (path != null && path.isValid() && containsPath(path)) {
            return map.get(path); }
        else { throw new PathNotFoundException(path); }
    }

    private void unWeightedDist() {
        //System.err.println("ji suan");
        for (int v : lgraph.keySet()) {
            HashMap<Integer, Integer> dm = new HashMap<>();
            for (int to : lgraph.keySet()) {
                if (to == v) { dm.put(to, 0); }
                else { dm.put(to, -1); }
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
                if (i == num) { break; }
            }
            dist.put(v,distm);
        }
    }

    private void changeStatus() {
        isDestroy = true;
        blockDestroy = true;
    }

    private void flushCache() {
        if (blockDestroy) {
            traDist = new HashMap<>();
            priDist = new HashMap<>();
            pleDist = new HashMap<>();
        }
    }

    private void add(int from, int to, int id) {
        if (lgraph.containsKey(from)) {
            HashMap<Integer, Integer> hm = lgraph.get(from);
            if (hm.containsKey(to)) { hm.put(to,hm.get(to) + 1); }
            else {
                hm.put(to,1);
                changeStatus(); //加入了新的边 破坏了图
            }
        } else {
            HashMap<Integer, Integer> hm = new HashMap<>();
            hm.put(to,1);
            lgraph.put(from,hm);
            changeStatus(); //加入了新的边 破坏了图
        }
        if (from != to) {
            if (graph.containsKey(new Pair<>(from,id))) {
                graph.get(new Pair<>(from,id)).add(new Pair<>(to,id));
            } else {
                HashSet<Pair<Integer,Integer>> set = new HashSet<>();
                set.add(new Pair<>(to, id));
                graph.put(new Pair<>(from, id),set);
            }
        }
    }

    private void addIdInPath(int from, int id) {
        if (!graph.containsKey(new Pair<>(from,-1))) { //起点
            graph.put(new Pair<>(from,-1),new HashSet<>());
        }
        graph.get(new Pair<>(from,-1)).add(new Pair<>(from,id));
        if (!graph.containsKey(new Pair<>(from,0))) { //终点
            graph.put(new Pair<>(from,0),new HashSet<>());
        }
        graph.get(new Pair<>(from,0)).add(new Pair<>(from,-1));
        if (graph.containsKey(new Pair<>(from,id))) {
            graph.get(new Pair<>(from, id)).add(new Pair<>(from, 0));
        }
    }

    @Override
    public int addPath(Path path) {
        if (path != null && path.isValid()) {
            if (!containsPath(path)) {
                maxid++;
                map.put(path,maxid);
                idmap.put(maxid,path);
                for (Integer id : path) {
                    if (dismap.containsKey(id)) {
                        dismap.put(id,dismap.get(id) + 1);
                    } else {
                        dismap.put(id,1);
                        changeStatus(); //加入了新的点 破坏了图
                    }
                }
                for (int i = 0;i < path.size() - 1; i++) {
                    int from = path.getNode(i);
                    int to = path.getNode(i + 1);
                    add(from,to,maxid);
                    add(to,from,maxid);
                    if (from != to) { addIdInPath(from,maxid); }
                }
                int from = path.getNode(path.size() - 1);
                addIdInPath(from, maxid);
                flushCache();
                //System.err.println(graph);
                return maxid;
            } else { return map.get(path); }
        } else { return 0; }
    }

    private void removeIdInPath(int from,int id) {
        if (graph.containsKey(new Pair<>(from,-1))) {
            graph.get(new Pair<>(from,-1)).remove(new Pair<>(from,id));
            if (graph.get(new Pair<>(from,-1)).size() == 0) {
                graph.remove(new Pair<>(from,-1));
                graph.remove(new Pair<>(from,0));
            }
        }
        graph.remove(new Pair<>(from,id));
    }

    private void remove(int from,int to) {
        HashMap<Integer, Integer> hm = lgraph.get(from);
        if (hm.get(to) == 1) {
            hm.remove(to);
            changeStatus(); //删除了边 破坏了图
        } else { hm.put(to,hm.get(to) - 1); } //只是减少了重边 没有破坏图
        if (hm.size() == 0) {
            lgraph.remove(from);
            dist.remove(from);
            changeStatus(); //删除了边 破坏了图
        }
    }

    private void mapRemove(int id,Path path) {
        map.remove(path);
        idmap.remove(id);
        for (Integer i : path) {
            if (dismap.get(i) == 1) {
                dismap.remove(i);
                changeStatus(); //删除了某个点 破坏了图
            } else { dismap.put(i,dismap.get(i) - 1); }
        }
        for (int i = 0;i < path.size() - 1; i++) {
            int from = path.getNode(i);
            int to = path.getNode(i + 1);
            remove(from,to);
            remove(to,from);
            if (from != to) { removeIdInPath(from,id); }
        }
        int from = path.getNode(path.size() - 1);
        removeIdInPath(from,id);
    }

    @Override
    public int removePath(Path path) throws PathNotFoundException {
        if (path != null && path.isValid() && containsPath(path)) {
            int id = map.get(path);
            mapRemove(id,path);
            flushCache();
            return id;
        } else { throw new PathNotFoundException(path); }
    }

    @Override
    public void removePathById(int pathId) throws PathIdNotFoundException {
        if (containsPathId(pathId)) {
            Path path = idmap.get(pathId);
            mapRemove(pathId,path);
            flushCache();
        } else { throw new PathIdNotFoundException(pathId); }
    }

    @Override
    public /*@pure@*/int getDistinctNodeCount() { return dismap.size(); }

    private int solveWeight(int kind,Pair<Integer,Integer> p1,
                            Pair<Integer,Integer> p2) {
        if (kind == 1) { //换乘
            if (p1.getValue().equals(p2.getValue())) { return 0; }
            else {
                if (p1.getValue() == 0 && p2.getValue() == -1) { return 1; }
                assert p1.getKey().equals(p2.getKey());
                return 0;
            }
        } else if (kind == 2) { //票价
            if (p1.getValue().equals(p2.getValue())) { return 1; }
            else {
                if (p1.getValue() == 0 && p2.getValue() == -1) { return 2; }
                assert p1.getKey().equals(p2.getKey());
                return 0;
            }
        } else if (kind == 3) { //不满意度
            if (p1.getValue().equals(p2.getValue())) { //同一条线
                int t = Math.max(((p1.getKey() % 5 + 5) % 5),
                        ((p2.getKey() % 5 + 5) % 5));
                if (t == 0) { return 1; }
                else if (t == 1) { return 4; }
                else if (t == 2) { return 16; }
                else if (t == 3) { return 64; }
                else { return 256; }
            } else {
                if (p1.getValue() == 0 && p2.getValue() == -1) { return 32; }
                assert p1.getKey().equals(p2.getKey());
                return 0;
            }
        }
        return 0;
    }

    private HashMap<Integer,HashMap<Integer,Integer>> selectDist(int kind) {
        if (kind == 1) { return traDist; }
        else if (kind == 2) { return priDist; }
        else if (kind == 3) { return  pleDist; }
        else { return new HashMap<>(); }
    }

    private void storeRes(int kind,Pair<Integer,Integer> from,
                             Pair<Integer,Integer> to,int res) {
        HashMap<Integer,HashMap<Integer,Integer>> dist = selectDist(kind);
        if (!dist.containsKey(from.getKey())) {
            dist.put(from.getKey(),new HashMap<>());
        }
        HashMap<Integer, Integer> graphd = dist.get(from.getKey());
        if (!graphd.containsKey(to.getKey())) { graphd.put(to.getKey(),res); }
        else if (graphd.get(to.getKey()) > res) { graphd.put(to.getKey(),res); }
    }

    private void dijkstra(int v,int kind) {
        Main.cnt++;
        HashSet<Pair<Integer,Integer>> collect = new HashSet<>();
        HashMap<Pair<Integer,Integer>, Integer> dm = new HashMap<>();
        Pair<Integer,Integer> root = new Pair<>(v,-1);  //起点
        for (Pair<Integer,Integer> pair : graph.keySet()) {
            dm.put(pair,Integer.MAX_VALUE);
            collect.add(pair);
        }
        PriorityQueue<Point> queue = new PriorityQueue<>();
        queue.add(new Point(root,0));
        dm.put(root,0);
        while (!queue.isEmpty()) {
            Point tmp = queue.poll();
            if (tmp.getDist() == Integer.MAX_VALUE) { break; }
            if (!collect.contains(tmp.getPair())) { continue; }
            collect.remove(tmp.getPair());
            HashSet<Pair<Integer,Integer>> set = graph.get(tmp.getPair());
            for (Pair<Integer,Integer> p : set) {
                if (collect.contains(p)) {
                    int d = tmp.getDist() + solveWeight(kind,tmp.getPair(),p);
                    if (d < dm.get(p)) {
                        dm.put(p,d);
                        queue.offer(new Point(p,d));
                    }
                }
            }
        }
        for (Pair<Integer,Integer> pair : dm.keySet()) {
            storeRes(kind,root,pair,dm.get(pair));
            storeRes(kind,pair,root,dm.get(pair));
        }
    }

    private int solveDijkstra(int fromNodeId,int toNodeId,int kind)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        } else if (!containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        } else {
            if (isConnected(fromNodeId,toNodeId)) {
                HashMap<Integer,HashMap<Integer,Integer>> d = selectDist(kind);
                if (d.containsKey(fromNodeId) &&
                        d.get(fromNodeId).containsKey(toNodeId)) { //先查缓存
                    return d.get(fromNodeId).get(toNodeId);
                } else {
                    dijkstra(fromNodeId, kind);
                    return d.get(fromNodeId).get(toNodeId);
                }
            } else { throw new NodeNotConnectedException(fromNodeId,toNodeId); }
        }
    }

    @Override
    public int getLeastTransferCount(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        return solveDijkstra(fromNodeId,toNodeId,1);
    }

    @Override
    public int getLeastTicketPrice(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        return solveDijkstra(fromNodeId,toNodeId,2);
    }

    @Override
    public int getLeastUnpleasantValue(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        return solveDijkstra(fromNodeId,toNodeId,3);
    }

    private void bfs(int v) {
        vis.put(v,1);
        LinkedList<Integer> queue = new LinkedList<>();
        queue.addLast(v);
        int i = 1;
        while (!queue.isEmpty()) {
            int tmp = queue.removeFirst();
            HashMap<Integer, Integer> hm = lgraph.get(tmp); //找邻接点
            for (int to : hm.keySet()) {
                if (vis.get(to) == 0) {
                    vis.put(to,1);
                    queue.addLast(to);
                    i++;
                    if (i == lgraph.size()) { return; }
                }
            }
        }
    }

    @Override
    public int getConnectedBlockCount() {
        if (blockDestroy) {
            //System.err.println("re bfs");
            for (int i : lgraph.keySet()) { vis.put(i, 0); }
            blockCnt = 0;
            for (int i : lgraph.keySet()) {
                if (vis.get(i) == 0) {
                    bfs(i);
                    blockCnt++;
                }
            }
            blockDestroy = false;
        }
        return blockCnt;
    }

    public /*@pure@*/ int getUnpleasantValue(
            Path path, int fromIndex, int toIndex) { return 0; }
}
