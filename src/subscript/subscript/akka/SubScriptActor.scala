package subscript.akka

import subscript.DSL._
import scala.collection.mutable.ListBuffer
import subscript.vm._
import subscript.vm.executor._
import subscript.vm.model.template._
import subscript.vm.model.template.concrete._
import akka.actor._
import subscript.vm.model.callgraph._

// was: import scala.actors.Logger
object Debug extends Logger("") {}
class Logger(tag: String) {
  private var lev = 2

  def level = lev
  def level_= (lev: Int) = { this.lev = lev }

  private val tagString = if (tag == "") "" else " ["+tag+"]"

  def info     (s: String)  = if (lev > 2) System.out.println(   "Info" + tagString + ": " + s)
  def warning  (s: String)  = if (lev > 1) System.err.println("Warning" + tagString + ": " + s)
  def error    (s: String)  = if (lev > 0) System.err.println(  "Error" + tagString + ": " + s)
  def doInfo   (b: => Unit) = if (lev > 2) b
  def doWarning(b: => Unit) = if (lev > 1) b
  def doError  (b: => Unit) = if (lev > 0) b
}
trait SubScriptActor extends Actor {
  
  val runner: SubScriptActorRunner = SSARunnerV1Scheduler
  
  private object Terminator { // TBD: find better name; something with Blocker
    var executor: EventHandlingCodeFragmentExecutor[N_code_eventhandling] = null
    
    def script block = @{executor = new EventHandlingCodeFragmentExecutor(there, there.scriptExecutor)}: {. .}
    def release = executor.executeMatching(isMatching=true)
  }
  
  private val callHandlers = ListBuffer[PartialFunction[Any, Unit]]()

  
  
  // Scripts
  def _live(): Script[Unit]
  private def script terminate = Terminator.block
  private def script die       = {if (context ne null) context stop self}
  
  def script r$(handler: PartialFunction[Any, Script[Any]]) 
  = var s:Script[Any]=null
    @{val here = there.parent.asInstanceOf[CallGraphTreeNode] // Bug: here is not yet known; is needed to access local variable s
      there.codeExecutor = EventHandlingCodeFragmentExecutor(there, there.scriptExecutor)
      val handlerWithExecuteAA = handler andThen {hr => {s = hr; there.codeExecutor.executeAA}}
                          synchronized {callHandlers += handlerWithExecuteAA}
      there.onDeactivate {synchronized {callHandlers -= handlerWithExecuteAA}}
    }: 
    {. Debug.info(s"$this.r$$") .}
    if s != null then s
  
  
  // Callbacks
  override def aroundPreStart() {
    Debug.info(s"$this aroundPreStart INIT")
    def script lifecycle = (live || terminate) ; die
    runner.launch([lifecycle])
    super.aroundPreStart()
    Debug.info(s"$this aroundPreStart EXIT")
  } 
  
  override def aroundReceive(receive: Actor.Receive, msg: Any) {    
    synchronized {
      sendSynchronizationMessage(this)
      wait()
    }
    
    runner.doScriptSteps
    var messageWasHandled = false
    callHandlers.synchronized {
      for (h <- callHandlers if !messageWasHandled && (h isDefinedAt msg)) {
        h(msg)  // TBD: check for success; requires access to the VM node
        messageWasHandled = true
      }
    }
    if (messageWasHandled) {
         runner.doScriptSteps
         Debug.info(s"$this aroundReceive handled  sender: $sender msg: $msg")}
    else Debug.info(s"$this aroundReceive did NOT handle msg   sender: $sender msg: $msg")
    
    // If a message was handled, Akka will try to match it against a function that can handle any message
    // otherwise it will try to match the message against function that can handle virtually nothing
    // (except LocalObject, which is certainly local and can't be available from the outside)
    case object LocalObject
    super.aroundReceive(if (messageWasHandled) {case _: Any =>} else {case LocalObject =>}, msg)
  }
  
  override def aroundPostStop() {
    Terminator.release
    super.aroundPostStop()
  }
  
  final def receive: Actor.Receive = {case _ =>} 
  
    
  def sendSynchronizationMessage(lock: AnyRef) {
    val vm = runner.executor
    vm insert SynchronizationMessage(vm.rootNode, lock)    
  }

}

case class SynchronizationMessage(node: CallGraphNode, lock: AnyRef) extends CallGraphMessageN {
  type N = CallGraphNode
  override def priority = PRIORITY_InvokeFromET - 1  // After all actors are launched
}
