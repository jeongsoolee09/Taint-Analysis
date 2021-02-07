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
package com.stratio.decision.functions.ddl;

import com.stratio.decision.commons.constants.ColumnType;
import com.stratio.decision.commons.constants.STREAM_OPERATIONS;
import com.stratio.decision.commons.messages.ColumnNameTypeValue;
import com.stratio.decision.functions.ActionBaseFunctionHelper;
import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.LinkedList;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by aitor on 9/23/15.
 */
public class DDLActionsFunctionTest extends ActionBaseFunctionHelper {

    private static final Logger LOGGER = LoggerFactory.getLogger(DDLActionsFunctionTest.class);



    @Before
    public void setUp() throws Exception {
        LOGGER.debug("Initializing required classes");
        initialize();
    }

    @Test
    public void testAddQueryToStreamFunction() throws Exception {

        AddQueryToStreamFunction func= new AddQueryToStreamFunction(streamOperationsService, ZOO_HOST);
        assertEquals("Expected operation not found", STREAM_OPERATIONS.DEFINITION.ADD_QUERY, func.getStartOperationCommand());
        assertEquals("Expected operation not found", STREAM_OPERATIONS.DEFINITION.REMOVE_QUERY, func.getStopOperationCommand());

        assertTrue("Not true value found", func.startAction(message));
        assertTrue("Not true value found", func.stopAction(message));

        func.addStartRequestsValidations(validators);
        func.addStopRequestsValidations(validators);
    }


    @Test
    public void testAlterStreamFunction() throws Exception {

        AlterStreamFunction func= new AlterStreamFunction(streamOperationsService, ZOO_HOST);
        assertEquals("Expected operation not found", STREAM_OPERATIONS.DEFINITION.ALTER, func.getStartOperationCommand());
        assertEquals("Expected null value not found", null, func.getStopOperationCommand());

        message.setColumns(new LinkedList<ColumnNameTypeValue>() {{
            new ColumnNameTypeValue("newcolumn", ColumnType.STRING, "newcolumn");
        }});

        assertTrue("Not true value found", func.startAction(message));
        assertTrue("Not true value found", func.stopAction(message));

        func.addStartRequestsValidations(validators);
        func.addStopRequestsValidations(validators);
    }


    @Test
    public void testCreateStreamFunction() throws Exception {

        CreateStreamFunction func= new CreateStreamFunction(streamOperationsService, ZOO_HOST);
        assertEquals("Expected operation not found", STREAM_OPERATIONS.DEFINITION.CREATE, func.getStartOperationCommand());
        assertEquals("Expected operation not found", STREAM_OPERATIONS.DEFINITION.DROP, func.getStopOperationCommand());

        assertTrue("Not true value found", func.startAction(message));
        assertTrue("Not true value found", func.stopAction(message));

        func.addStartRequestsValidations(validators);
        func.addStopRequestsValidations(validators);
    }
}