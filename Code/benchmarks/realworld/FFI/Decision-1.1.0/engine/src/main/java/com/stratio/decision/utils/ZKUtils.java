/**
 * Copyright (C) 2014 Stratio (http://stratio.com)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *         http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.stratio.decision.utils;

import java.util.Date;
import java.util.Iterator;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.apache.curator.framework.CuratorFramework;
import org.apache.curator.framework.CuratorFrameworkFactory;
import org.apache.curator.framework.imps.CuratorFrameworkState;
import org.apache.curator.retry.ExponentialBackoffRetry;
import org.apache.zookeeper.CreateMode;
import org.apache.zookeeper.data.Stat;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.gson.Gson;
import com.stratio.decision.commons.constants.STREAMING;
import com.stratio.decision.commons.constants.STREAM_OPERATIONS;
import com.stratio.decision.commons.messages.StratioStreamingMessage;

public class ZKUtils {

    private static Logger logger = LoggerFactory.getLogger(ZKUtils.class);

    private static ZKUtils self;
    private CuratorFramework client;
    private ExecutorService backgroundZookeeperCleanerTasks;
    private String groupId;

    private ZKUtils(String zookeeperCluster) throws Exception {

        this(zookeeperCluster, null);
    }

    private ZKUtils(String zookeeperCluster, String groupId) throws Exception {

        this.groupId = groupId;

        // ZOOKEPER CONNECTION
        client = CuratorFrameworkFactory.newClient(zookeeperCluster, 25 * 1000, 10 * 1000, new ExponentialBackoffRetry(
                1000, 3));
        client.start();
        client.getZookeeperClient().blockUntilConnectedOrTimedOut();

        if (client.getState().compareTo(CuratorFrameworkState.STARTED) != 0) {
            throw new Exception("Connection to Zookeeper timed out after seconds");
        } else {
            backgroundZookeeperCleanerTasks = Executors.newFixedThreadPool(1);
            backgroundZookeeperCleanerTasks.submit(new ZookeeperBackgroundCleaner(client, groupId));
        }


    }

    public static ZKUtils getZKUtils(String zookeeperCluster) throws Exception {
        if (self == null) {
            self = new ZKUtils(zookeeperCluster);
        }
        return self;
    }

    public static ZKUtils getZKUtils(String zookeeperCluster, String groupId) throws Exception {
        if (self == null) {
            self = new ZKUtils(zookeeperCluster, groupId);
        }
        return self;
    }



    public static void shutdownZKUtils() {
        if (self != null) {
            self.backgroundZookeeperCleanerTasks.shutdownNow();
            self.client.close();
        }
    }

    public void createEphemeralZNode(String path, byte[] data) throws Exception {

        if (client.checkExists().forPath(path) != null) {
            client.delete().deletingChildrenIfNeeded().forPath(path);
        }

        client.create().creatingParentsIfNeeded().withMode(CreateMode.EPHEMERAL).forPath(path, data);
    }

    public void createPath(String path) throws Exception {
        if (client.checkExists().forPath(path) != null) {
            logger.debug("Path already exists " + path);
        }   else    {
            client.create().creatingParentsIfNeeded().forPath(path);
        }

    }

    public void createZNodeJsonReply(StratioStreamingMessage request, Object reply) throws Exception {


//        String path = STREAMING.ZK_BASE_PATH + "/" + request.getOperation().toLowerCase() + "/"
//                    + request.getRequest_id();
//
//
//        if (client.checkExists().forPath(path) != null) {
//            client.delete().deletingChildrenIfNeeded().forPath(path);
//        }
//
//        client.create().creatingParentsIfNeeded().forPath(path, new Gson().toJson(reply).getBytes());

        String path = STREAMING.ZK_BASE_PATH + "/" + request.getOperation().toLowerCase() + "/"
                + request.getRequest_id();

        createZNodeJsonReplyForPath(request, reply, path);


        logger.info("**** ZKUTILS " + request.getOperation() + "//" + request.getRequest_id() + "//" + reply + "//"
                + path);

    }



    public String getTempZNodeJsonReplyPath(StratioStreamingMessage request){

        return STREAMING.ZK_BASE_PATH + "/" + request.getOperation().toLowerCase() + "/ack" + "/"
                + request.getRequest_id() ;

    }

    public void createTempZNodeJsonReply(StratioStreamingMessage request, Object reply, String groupId) throws Exception {


        String path = getTempZNodeJsonReplyPath(request) + "/" + groupId;

        createZNodeJsonReplyForPath(request, reply, path);

        logger.info("**** ZKUTILS. Temporal ack Node " + request.getOperation() + "//" + request.getRequest_id() +
                "//" + reply + "//" + path);

    }


    private void createZNodeJsonReplyForPath(StratioStreamingMessage request, Object reply, String path) throws
            Exception {

        if (client.checkExists().forPath(path) != null) {
            client.delete().deletingChildrenIfNeeded().forPath(path);
        }

        client.create().creatingParentsIfNeeded().forPath(path, new Gson().toJson(reply).getBytes());
    }


    public void createZNode(String path, byte[] data) throws Exception {
        if (client.checkExists().forPath(path) != null) {
            client.delete().deletingChildrenIfNeeded().forPath(path);
        }

        client.create().creatingParentsIfNeeded().withMode(CreateMode.PERSISTENT).forPath(path, data);
    }

    public byte[] getZNode(String path) throws Exception {
        return client.getData().forPath(path);
    }

    public boolean existZNode(String path) throws Exception {
        Stat stat = client.checkExists().forPath(path);
        return (stat == null) ? false : true;
    }

    private class ZookeeperBackgroundCleaner implements Runnable {

        private Logger logger = LoggerFactory.getLogger(ZookeeperBackgroundCleaner.class);

        private CuratorFramework client;
        private String groupId;
        private static final long ZNODES_TTL = 600000; // 10 minutes
        private static final long CLEAN_INTERVAL = 300000; // 5 minutes
        private static final long MAX_LIVE_FOR_OPERATION_NODE = 60000; // 1 minute

        /**
         *
         */
        public ZookeeperBackgroundCleaner(CuratorFramework client) {
            this.client = client;
            logger.debug("Starting ZookeeperBackgroundCleaner...");
            logger.info("ZookeeperBackgroundCleaner BASE path " + STREAMING.ZK_BASE_PATH);
        }

        public ZookeeperBackgroundCleaner(CuratorFramework client, String groupId) {

            this(client);
            this.groupId = groupId;

        }

        private int removeOldChildZnodes(String path) throws Exception {

            int counter = 0;
            Iterator<String> children = client.getChildren().forPath(path).iterator();

            while (children.hasNext()) {

                String childrenPath = children.next();
                if (!STREAMING.ZK_HIGH_AVAILABILITY_NODE.equals('/'+childrenPath) && !STREAMING.ZK_PERSISTENCE_NODE.equals('/'+childrenPath)) {
                    if (client.getChildren().forPath(path + "/" + childrenPath).size() > 0) {
                        counter += removeOldChildZnodes(path + "/" + childrenPath);
                    } else {

                        Stat znode = client.checkExists().forPath(path + "/" + childrenPath);
                        Boolean deleteNode = true;
                        // avoid nulls and ephemeral znodes
                        if (znode != null && znode.getEphemeralOwner() == 0) {

                            String parentPath = path.substring(path.lastIndexOf("/") +1);

                            if (STREAM_OPERATIONS.SyncOperations.getAckOperations().contains(parentPath)) {

                                if ( new Date().getTime() - znode.getMtime() < MAX_LIVE_FOR_OPERATION_NODE) {
                                    deleteNode = false;
                                }
                            }

                            if (deleteNode) {
                                client.delete().deletingChildrenIfNeeded().forPath(path + "/" + childrenPath);
                                counter++;
                            }
                        }

                    }
                }
            }

            return counter;
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.lang.Runnable#run()
         */
        @Override
        public void run() {

            String zkPath = STREAMING.ZK_BASE_PATH;
/*
            if (groupId != null){
                zkPath = zkPath.concat("/").concat(groupId);
            }
*/
            while (!Thread.currentThread().isInterrupted()) {

                try {

                    if (client.getState().compareTo(CuratorFrameworkState.STARTED) == 0) {

                        int childsRemoved = removeOldChildZnodes(zkPath);
                        logger.debug(childsRemoved + " old zNodes removed from ZK");
                    }

                    Thread.sleep(CLEAN_INTERVAL);

                } catch (InterruptedException ie) {
                    // no need to clean anything, as client is shared
                    logger.info("Shutting down Zookeeper Background Cleaner");
                }

                catch (Exception e) {
                    logger.info("Error on Zookeeper Background Cleaner: " + e.getMessage());
                }

            }

        }

    }

}
