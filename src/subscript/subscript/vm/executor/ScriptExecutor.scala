package subscript.vm.executor

import scala.util.{Try}
import subscript.vm._
import subscript.vm.executor.data._
import subscript.vm.executor.parts._
import subscript.DSL._
import scala.collection.mutable.Buffer
import subscript.vm.executor.data.MessageHandlers.MessageHandler
import subscript.vm.model.callgraph.ScriptResultHolder

object ScriptExecutorFactory {
  var scriptDebuggerQueue = new scala.collection.mutable.Queue[MsgListener]
  def addScriptDebugger(sd: MsgListener) = {
    //println("addScriptDebugger: "+sd.getClass.getCanonicalName)
    scriptDebuggerQueue += sd
  }
  def createScriptExecutor[S](allowDebugger: Boolean) = {
    val se = new CommonScriptExecutor[S]
    if (allowDebugger && !scriptDebuggerQueue.isEmpty) {
      val h = scriptDebuggerQueue.head
      //println("createScriptExecutor: "+se+ " Debugger: "+h.getClass.getCanonicalName)
      scriptDebuggerQueue = scriptDebuggerQueue.tail
      h.attach(se)
    }
    //else println("createScriptExecutor: "+se+" allowDebugger: "+allowDebugger+" scriptDebuggerQueue.isEmpty: "+scriptDebuggerQueue.isEmpty)
    se
  }
}

trait ScriptExecutor[S] extends MsgPublisher with TaskSupplyInterface with Tracer with OldApi with ScriptResultHolder[S] {
  // Internal state
  // TBD: change restriction from `subscript` to `vm`

  var traceLevel: Int
  
  val stateAccessLock = new Object
  val msgQueue        = new MessageQueue   (stateAccessLock) with MQExtras with TrackToBeExecuted
  val msgHandlers     = new MessageHandlers(stateAccessLock)
  val graph           = new CallGraph(this)
  
  def hasSuccess: Boolean = graph.rootNode.hasSuccess
  def hasActiveProcesses = !graph.rootNode.children.isEmpty

  def doCodeThatInsertsMsgs_synchronized(code: =>Unit): Unit
 
  // Initialization
  graph.init()
  
  // Lifecycle methods
  /**
   * Launches this VM to execute given script.
   */
  def run[R<:S](s: ScriptNode[R]): ScriptExecutor[S]
  
  /**
   * Performs initialization before this VM starts working.
   * Must be called before VM starts operating.
   * Must be called exactly once.
   */
  def initializeExecution[R<:S](s: ScriptNode[R]): Unit
  
  /**
   * Tries to dequeue and handle message from the messages queue.
   */
  def tryHandleMessage(minimalPriorityForAA: Int): CallGraphMessage
  
  /**
   * Applies each registered handler to a given message, if
   * this handler is defined over this message.
   */
  def handle(message: CallGraphMessage): Unit
  
  /**
   * Specifies the logic to be executed when there are no
   * more messages to handle, but they are expected in future
   */
  def awaitMessages: Unit
  
  /**
   * Synchronizes all the collections in a thread-safe manner.
   */
  def updateCollections() = stateAccessLock.synchronized {
    msgQueue   .commit()
    msgHandlers.commit()
  }
}

abstract class AbstractScriptExecutor[S] extends ScriptExecutor[S] {
  // Initialization
  msgQueue addListener this
  
  // Lifecycle methods  
  /**
   * Performs initialization before this VM starts working.
   * Must be called before VM starts operating.
   * Must be called exactly once.
   */
  def initializeExecution[R<:S](s: ScriptNode[R]) {
    val anchorNode = graph.anchorNode
    CallGraph.connect(parentNode = anchorNode, childNode = s) // code duplicated from Callgraph.activateFrom
    msgQueue insert Activation(s)                             // idem
  }
  
  /**
   * Tries to dequeue and handle message from the messages queue.
   */
  def tryHandleMessage(minimalPriorityForAA: Int): CallGraphMessage = {
    val m = msgQueue.dequeue(minimalPriorityForAA)
    if (m == null) return null
    messageHandled(m)
    handle(m)
    m
  }
  
  /**
   * Applies each registered handler to a given message, if
   * this handler is defined over this message.
   */
  def handle(message: CallGraphMessage): Unit =
    for (h <- msgHandlers.collection if h isDefinedAt message) h(message)
}

class CommonScriptExecutor[S] extends AbstractScriptExecutor[S] with Tracer with
    DefaultHandlers {
  var traceLevel = 0

  msgQueue addListener new MessageQueuedNotifier(this)
  msgHandlers sInsert defaultHandler
  msgHandlers sInsert communicationHandler
  msgHandlers sInsert continuationHandler
  
  def run[R<:S](s: ScriptNode[R]) = {
    initializeExecution(s)
    while (hasActiveProcesses) {
      updateCollections()
      if (tryHandleMessage(Int.MinValue)==null) awaitMessages
    }
    $ = s.$
    this
  }
  
  def awaitMessages {
    trace("awaitMessages")
    messageAwaiting
    synchronized { // TBD: there should also be a synchronized call in the CodeExecutors
      if (msgQueue.collection.size == 0) { // looks stupid, but event may have happened&notify() may have been called during tracing
          trace("wait - start")
          wait() // for an event to happen 
          trace("wait - end")
      }
    }
    // note: there may also be deadlock because of unmatching communications
    // so there should preferably be a check for the existence of waiting event handling actions
  }
  
  /*
   * Execute the given code that may insert some call graph messages into the message queue.
   * This must be done in a synchronized way, and it may need to cause the call to wait()
   * in awaitMessages to end. Therefore this method does notify as well.
   */
  def doCodeThatInsertsMsgs_synchronized(code: =>Unit): Unit = synchronized{ code; notify }
}

/**
 * This is for compatibility with not yet refactored part of the VM.
 */
trait OldApi {this: ScriptExecutor[_] =>
  def insert(m: CallGraphMessage) = msgQueue insert /*sInsert*/ m  // TBD: do sInsert here
  def insert_traced(m: CallGraphMessage) = {
    trace_nonl(s"(inserting ${m.getClass}...")
    insert(m)  
    trace_nonl("done)")
  }
  def rootNode = graph.rootNode
  def addHandler(h: MessageHandler) = msgHandlers sInsert h
}
