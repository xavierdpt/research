https://en.wikipedia.org/wiki/Business_process_modeling
https://en.wikipedia.org/wiki/Business_Process_Modeling_Language
https://en.wikipedia.org/wiki/Business_Process_Execution_Language
https://en.wikipedia.org/wiki/Business_Process_Model_and_Notation

=== BPML : Dead ==

XML
BPMI Business Process Management Initiative 
OMG Object Management Group
BMI DTF Business Modeling and Integration Domain Task Force

Deprecated since 2008

BPML is a superset of BPEL ; not implemented by BizTalk or WebSphere ; focus on BPEL

BPML is dead ; long live BPEL4WS or BPDM

BPDM : https://en.wikipedia.org/wiki/Business_Process_Definition_Metamodel

BPMS : Business Process Management System

BPEL is not a complete process language

In practice BPEL is often used in conjunction with Java to fill in the "missing" semantics. 
BPEL is often tied to proprietary implementations of workflow or integration broker engines.

BPML was designed, and implemented, as a pure concurrent and distributed processing engine.
BPML was designed to be semantically complete according to the Pi-calculus formal representation of computational processes.

https://en.wikipedia.org/wiki/Process-oriented_programming

=== BPDM ==

XSD : XML Schema
XMI : XML for Metadata Interchange

One Goal : make sure models are interpreted the same way when moved to a different tool

BPDM choregraphy : extension of BPMN and BPEL to independent business processes executing in different business units

A choreography can be specified independently of its participants, and used as a requirement for the specification of the orchestration implemented by a participant.

BPDM provides for the binding of orchestration to choreography to ensure compatibility.

BPDM can be an alternative to XPDL

XPDL: XML Process Definition Language

BPDM provides a specification of semantics integrated in a metamodel

=== BPMN ===

https://en.wikipedia.org/wiki/Business_Process_Model_and_Notation

graphical representation

BPMN 2.0 January 2011

BPD: Business Process Diagram

similarity with activity diagrams in UML

Mapping to BPEL

Goal: bridge the gap between business process design and implementation

2014 : Decision Model and Notation : new standard

Flow objects: events, activities, gateways
Connecting objects: sequence flow, message flow, association
Swim lanes : Pool, lane https://en.wikipedia.org/wiki/Swim_lane
Artifacts: Data object, group, annotation

Event: circle, represents something that happens, has a type, catching or throwing
Start, intermediate and end events.
Start is catching only, end is throwing only.

Activity: Rounded-corner
Tasks, sub-processe, transactions, call activity

Gateway: exclusive, event-based, parallel, inclusive, exclusive-event-based, complex, parallel-event-based

Connections: sequence flow, message flow, association

Pool and lanes

BPMN 2.0: aligns to BPDM

The mapping from BPMN to BPEL is quite informal.

Synchronization between BPMN and BPEL is difficult.

Trisotech, jBPM, Edraw Max

=== jBPM ===

https://en.wikipedia.org/wiki/JBPM

Java open source

BPMN 2.0

Input : BPMN

Based on the Process Virtual Machine

Eclipse tools

Case management : CMMN

Can be used in traditional JEE applications and SpringBoot

=== BPEL ===

https://en.wikipedia.org/wiki/Business_Process_Execution_Language

WS-BPEL: Web Services Business Process Execution Language

OASIS standard

Origins: WSFL (Microsoft) and Xlang (IBM)

WSFL: Web Services Flow Language

BPEL4WS is Microsoft own weird mix for BizTalk

BPEL is based on Microsoft's thing

2007: BPEL4People and WS-HumanTask

BPEL is an orchestration language
It is not a choregraphy language

BPEL uses WSDL 1.1

No standard graphical notation for BPEL

BPMN is substantially different.

BPELJ and JSR 207

BPEL4People: the absence of human interactions was a significant gap for many real-world business processes =>  orchestration of role-based human activities

Why do we actually need the Pi-Calculus for Business Process Management ?
https://bpt.hpi.uni-potsdam.de/pub/Public/FrankPuhlmann/BIS2006-PIC.pdf


