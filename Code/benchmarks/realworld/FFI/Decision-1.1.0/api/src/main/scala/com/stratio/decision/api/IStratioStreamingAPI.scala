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
package com.stratio.decision.api

import java.util.List

import _root_.kafka.consumer.KafkaStream
import com.stratio.decision.api.dto.StratioQueryStream
import com.stratio.decision.api.messaging.{ColumnNameType, ColumnNameValue}
import com.stratio.decision.commons.exceptions._
import com.stratio.decision.commons.messages.{ColumnNameTypeValue, StratioStreamingMessage}
import com.stratio.decision.commons.streams.StratioStream

trait IStratioStreamingAPI {
  /**
   * Initializes the StratioStreamingAPI instance.
   * @return
   */
  @Deprecated
  @throws(classOf[StratioEngineConnectionException])
  def initialize(): IStratioStreamingAPI

  /**
   * Initializes the StratioStreamingAPI instance.
   * @param kafkaServer
   * @param kafkaPort
   * @param theZookeeperServer
   * @param theZookeeperPort
   * @param theZookeeperPath
   * @return
   */
  @Deprecated
  @throws(classOf[StratioEngineConnectionException])
  def initializeWithServerConfig(kafkaServer: String,
                                 kafkaPort: Int,
                                 theZookeeperServer: String,
                                 theZookeeperPort: Int,
                                 theZookeeperPath: String): IStratioStreamingAPI


  /**
    * Create a new instance of IStratioStreamingAPI, but streaming engine is not called.
    * To call to streaming engine, use init() method.
    * @param kafkaQuorum Format: host1:port1,host2:port2
    * @param zookeeperQuorum Format: host1:port1,host2:port2
    * @param zookeeperPath Format: /kafka
    * @return
    */
  def withQuorumConfig(
                        kafkaQuorum: String,
                        zookeeperQuorum: String,
                        zookeeperPath: String): IStratioStreamingAPI

  /**
   * Create a new instance of IStratioStreamingAPI, but streaming engine is not called.
   * To call to streaming engine, use init() method.
   * @param kafkaQuorum Format: host1:port1,host2:port2
   * @param zookeeperQuorum Format: host1:port1,host2:port2
   * @return
   */
  def withServerConfig(
                        kafkaQuorum: String,
                        zookeeperQuorum: String): IStratioStreamingAPI

  /**
   * Create a new instance of IStratioStreamingAPI, but streaming engine is not called.
   * To call to streaming engine, use init() method.
   * @param kafkaHost
   * @param kafkaPort
   * @param zookeeperHost
   * @param zookeeperPort
   * @return
   */
  def withServerConfig(
                        kafkaHost: String,
                        kafkaPort: Int,
                        zookeeperHost: String,
                        zookeeperPort: Int): IStratioStreamingAPI


  /**
    * If Decision is up but some of the nodes (group) of the cluster are down, we can continue inserting data
    * in kafka data topics
    */
  def insertWithGroupDown() : IStratioStreamingAPI

  /**
   * When server configuration is added, call this method to try to connect
   * to streaming engine async.
   * @throws StratioEngineConnectionException
   * @return
   */
  @throws(classOf[StratioEngineConnectionException])
  def init(): IStratioStreamingAPI;


  /**
   * Get if api is initialized correctly
   * @return
   */
  def isInit(): Boolean

  /**
   * Close all connections to decision engine.
   */
  def close

  /**
   * Check if stratio decision is running
   */
  def isConnected(): Boolean

  /**
   * Creates a new stream.
   * @param streamName
   * @param columns
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  @throws(classOf[StratioEngineOperationException])
  def createStream(streamName: String, columns: List[ColumnNameType])

  /**
   * Adds columns to a stream.
   * @param streamName
   * @param columns
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  @throws(classOf[StratioEngineOperationException])
  def alterStream(streamName: String, columns: List[ColumnNameType])

  /**
   * Inserts new data into a stream.
   * @param streamName
   * @param data
   * @param topicName
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  def insertData(streamName: String, data: List[ColumnNameValue], topicName: String = null, checkTopicExists:Boolean
  = false)

  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  def insertData(streamName: String, data: List[ColumnNameValue])


  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  def insertDataWithPartition(streamName: String, data: List[ColumnNameValue], keys: List[ColumnNameValue])


  /**
   * Adds a query to a stream.
   * @param streamName
   * @param query
   * @return the query Id
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  @throws(classOf[StratioEngineOperationException])
  def addQuery(streamName: String, query: String): String

  /**
   * Removes a query from a stream.
   * @param streamName
   * @param queryId
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioEngineOperationException])
  def removeQuery(streamName: String, queryId: String)

  /**
   * Removes a stream
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  @throws(classOf[StratioEngineOperationException])
  def dropStream(streamName: String)

  /**
   * Starts listening to a stream.
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  def listenStream(streamName: String): KafkaStream[String, StratioStreamingMessage]

  /**
   * Stops listening to a stream.
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPISecurityException])
  def stopListenStream(streamName: String)

  /**
   * Gets a list of the columns from a given stream.
   * @param stream
   * @throws StratioEngineOperationException
   * @return
   */
  @throws(classOf[StratioEngineOperationException])
  def columnsFromStream(stream: String): List[ColumnNameTypeValue]

  /**
   * Gets a list of the queries from a given stream.
   * @param stream
   * @throws StratioEngineOperationException
   * @return
   */
  @throws(classOf[StratioEngineOperationException])
  def queriesFromStream(stream: String): List[StratioQueryStream]

  /**
   * Gets a list of all the stream that currently exists.
   * @return a list with the streams
   */
  @throws(classOf[StratioEngineStatusException])
  @throws(classOf[StratioAPIGenericException])
  @throws(classOf[StratioEngineOperationException])
  def listStreams(): List[StratioStream]


  /**
    * Indexes the stream to the elasticsearch instance.
    */
  @throws(classOf[StratioEngineStatusException])
  def saveToElasticsearch(streamName : String)

  /**
    * Stops indexing the stream.
    */
  @throws(classOf[StratioEngineStatusException])
  def stopSaveToElasticsearch(streamName : String)

  /**
   * Indexes the stream to the elasticsearch instance.
   */
  @throws(classOf[StratioEngineStatusException])
  def indexStream(stream: String)

  /**
   * Stops indexing the stream.
   */
  @throws(classOf[StratioEngineStatusException])
  def stopIndexStream(stream: String)

  /**
   * Saves the stream to cassandra DB.
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  def saveToCassandra(streamName: String)

  /**
   * Stops saving the stream to cassandra DB.
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  def stopSaveToCassandra(streamName: String)

  /**
   * Saves the stream to MongoDB.
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  def saveToMongo(streamName: String)

  /**
   * Stops saving the stream to MongoDB.
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  def stopSaveToMongo(streamName: String)

  /**
   * Saves the stream to SolR.
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  def saveToSolr(streamName: String)

  /**
   * Stops saving the stream to Solr.
   * @param streamName
   */
  @throws(classOf[StratioEngineStatusException])
  def stopSaveToSolr(streamName: String)

  /**
    * Send the data of the stream to the Drools Engine
    * @param streamName
    * @param groupName
    * @param outputStream (optional)
    * @param kafkaTopic (optional)
    * @throws com.stratio.decision.commons.exceptions.StratioEngineStatusException
    */
  @throws(classOf[StratioEngineStatusException])
  def startSendToDrools(streamName: String, groupName: String, outputStream: String = null, kafkaTopic: String = null)

  /**
    * Stops sending the data to the Drools Engine
    * @param streamName
    * @throws com.stratio.decision.commons.exceptions.StratioEngineStatusException
    */
  @throws(classOf[StratioEngineStatusException])
  def stopSendToDrools(streamName: String)

  /**
   * Allows the client to define the time that the API
   * will wait for the engine responses.
   *
   * @param timeOutInMs
   * @throws StratioEngineStatusException
   */
  @throws(classOf[StratioEngineStatusException])
  def defineAcknowledgeTimeOut(timeOutInMs: Int): IStratioStreamingAPI
}
