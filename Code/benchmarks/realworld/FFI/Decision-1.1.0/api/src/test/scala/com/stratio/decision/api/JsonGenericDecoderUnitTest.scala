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

import com.stratio.decision.api.kafka.JsonGenericDecoder
import com.stratio.decision.commons.exceptions.StratioAPIGenericException
import org.junit.runner.RunWith
import org.scalatest._
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class JsonGenericDecoderUnitTest
  extends FunSpec
  with ShouldMatchers {

  describe("The json generic decoder") {
    it("should decode json to StratioStreamingMessage") {
      val jsonToBeParsed = """{"operation":"insert","streamName":"testStream","session_id":"1396942951802","request_id":"1396942953315","request":"","timestamp":1396942953315,"columns":[{"column":"field1","value":"testString"},{"column":"field2","value":200}],"userDefined":true}"""
      val jsonGenericDecoder = new JsonGenericDecoder
      val fieldsList = jsonGenericDecoder.fromBytes(jsonToBeParsed.getBytes)

      fieldsList.getColumns.size should be(2)
      fieldsList.getOperation should be("insert")
      fieldsList.getStreamName should be ("testStream")
    }

    it("should throw a StratioAPIGenericException when the json to be parsed is not-well formed") {
      val jsonToBeParsed = """{not well-formed json"""
      val jsonGenericDecoder = new JsonGenericDecoder
      intercept[StratioAPIGenericException] {
      jsonGenericDecoder.fromBytes(jsonToBeParsed.getBytes)
      }
    }
  }
}
