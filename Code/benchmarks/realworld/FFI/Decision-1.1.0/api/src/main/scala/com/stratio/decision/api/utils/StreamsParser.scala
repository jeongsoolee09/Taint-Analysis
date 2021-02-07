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
package com.stratio.decision.api.utils

import com.google.gson.Gson
import com.stratio.decision.commons.exceptions.StratioAPIGenericException
import com.stratio.decision.commons.messages.ListStreamsMessage
import com.stratio.decision.commons.streams.StratioStream

import scala.collection.JavaConversions._

object StreamsParser {
  val theGsonParser = new Gson()

  def parse(json: String) = {
    try {
      val listStreams = theGsonParser.fromJson(json, classOf[ListStreamsMessage]).getStreams.toList
      val stratioStreams = listStreams.map(stream => {
        new StratioStream(stream.getStreamName,
          stream.getColumns,
          stream.getQueries,
          stream.getActiveActions,
          stream.isUserDefined)}
      )
      stratioStreams
    } catch {
        case _: Throwable => throw new StratioAPIGenericException("Decision API error: unable to parse the json response")
    }

  }

}
