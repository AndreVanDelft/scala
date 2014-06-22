package subscript.vm.executor.parts

import subscript.vm._
import subscript.vm.executor._
import subscript.vm.executor.data._
import subscript.vm.model.template._
import subscript.vm.model.template.concrete._
import subscript.DSL._
import scala.collection.mutable.Buffer
import subscript.vm.model.callgraph._

/** To DATA section; don't change */
trait DefaultHandlers {this: ScriptExecutor[_] with Tracer =>
  import CodeExecutor._
  import CallGraph._
  import MessageHandlers._
  
  import msgQueue._
  import graph.{activateFrom, linkNode}
  
  /*
   * Handle an activation message.
   * This involves:
   * 
   * execute activation code, if defined
   * execute specific code, e.g. for if, while, script call
   * insert an activation message to create a child node
   */
  def handleActivation(message: Activation): Unit = {
      executeCodeIfDefined(message.node, message.node.onActivate)
      executeCodeIfDefined(message.node, message.node.onActivateOrResume)
      message.node match {
           //case n@N_root            (t: T_1_ary     ) => activateFrom(n, t.child0)
           case n@N_code_tiny                  (t)  => n.hasSuccess = true; executeCode(n); if (n.hasSuccess) doNeutral(n); insertDeactivation(n,null)
           case n@N_localvar                   (t)  => if (t.isLoop) setIteration_n_ary_op_ancestor(n);
            n.n_ary_op_ancestor.initLocalVariable(t.localVariable.name, n.pass, executeCode(n));doNeutral(n);insertDeactivation(n,null)
           case n@N_privatevar                 (t) => n.n_ary_op_ancestor.initLocalVariable(t.name, n.pass, n.getLocalVariableHolder(t.name).value)
           case n@N_code_normal                (_) => insert(AAActivated(n,null)); insert(AAToBeExecuted(n))
           case n@N_code_unsure                (_) => insert(AAActivated(n,null)); insert(AAToBeExecuted(n))
           case n@N_code_threaded              (_) => insert(AAActivated(n,null)); insert(AAToBeExecuted(n))

           case n@( N_code_eventhandling       (_) 
                  | N_code_eventhandling_loop  (_)) => // ehNodesAwaitingExecution.append(n) not used; could be handy for debugging
              
           case n@N_break                      (t) =>                                    doNeutral(n); insert(Break(n, null, ActivationMode.Inactive)); insertDeactivation(n,null)
           case n@N_optional_break             (t) =>                                    doNeutral(n); insert(Break(n, null, ActivationMode.Optional)); insertDeactivation(n,null)
           case n@N_optional_break_loop        (t) => setIteration_n_ary_op_ancestor(n); doNeutral(n); insert(Break(n, null, ActivationMode.Optional)); insertDeactivation(n,null)
           case n@N_loop                       (t) => setIteration_n_ary_op_ancestor(n); doNeutral(n); insertDeactivation(n,null)
           case n@N_delta                      (t) =>                     insertDeactivation(n,null)
           case n@N_epsilon                    (t) => insert(Success(n)); insertDeactivation(n,null)
           case n@N_nu                         (t) => doNeutral(n);       insertDeactivation(n,null)
           case n@N_while                      (t) => setIteration_n_ary_op_ancestor(n); 
                                                      n.hasSuccess = executeCode(n)
                                                      doNeutral(n)
                                                      if (!n.hasSuccess) {
                                                         insert(Break(n, null, ActivationMode.Inactive))
                                                      }
                                                      insertDeactivation(n,null)
                                                                       
           case n@N_launch                     (t) => activateFrom(CallGraphNode.getLowestLaunchAnchorAncestor(n), t.child0, Some(0)); doNeutral(n); insertDeactivation(n,null)
           case n@N_launch_anchor              (t) => activateFrom(n, t.child0, Some(0))
           case n@N_1_ary_op                   (t) => activateFrom(n, t.child0); insertContinuation1(message)
           case n@N_annotation                 (t) => activateFrom(n, t.child0); executeCode(n)
           case n@N_if                         (t) => if (executeCode(n)) activateFrom(n, t.child0) else {doNeutral(n); insertDeactivation(n,null)}
           case n@N_if_else                    (t) => if (executeCode(n)) activateFrom(n, t.child0) 
                                                                    else  activateFrom(n, t.child1)
           case n@N_do_then                    (t) => activateFrom(n, t.child0)
           case n@N_do_else                    (t) => activateFrom(n, t.child0)
           case n@N_do_then_else               (t) => activateFrom(n, t.child0)
           case n@N_n_ary_op                   (t, isLeftMerge) => val cn = activateFrom(n, t.children.head); if (!isLeftMerge) insertContinuation(message, cn)
           case n@N_call                       (t) => val s: Script[_] = executeCode(n)
                                                      if (n.t_callee!=null) linkNode(n, s, None)
                                                      else {
                                                        insert(CAActivated   (n,null))
                                                        insert(CAActivatedTBD(n))
                                                      }
           case n@Script                       (t, _*) => activateFrom(n, t.child0)   // ???????????
      }      
  }
  
  /*
   * Handle a deactivation message. 
   * If the receiving node is a n_ary operator and there is a sending child node,
   * then postpone further processing by inserting a continuation message.
   * TBD: add a case for a 1_ary operator
   * 
   * Insert deactivation messages for all parent nodes
   * Execute code for deactivation, if defined
   * Unlink the node from the call graph
   */
  def handleDeactivation(message: Deactivation): Unit = {
       message.node match {
           case n@N_n_ary_op (_: T_n_ary, _)  => if(!message.excluded
                                                 &&  message.child!=null) {
                                                   if (message.child.hasSuccess) {
                                                      n.childThatEndedInSuccess_index(message.child.index)
                                                   }
                                                   else {
                                                      n.aChildEndedInFailure = true
                                                   }
                                                   insertContinuation(message); 
                                                   return}
           case n@N_launch_anchor(_) => if (!n.children.isEmpty) return
           case n@N_do_then     (t)  => if (!message.excluded && message.child!=null
                                                              && message.child.template==t.child0 && !message.child.hasSuccess) {doNeutral(n); 
                                                                                                                                insertDeactivation(n,null); return} else if(!n.children.isEmpty) return
           case n@N_do_else     (t)  => if (!message.excluded && message.child.template==t.child0 && !message.child.hasSuccess) {activateFrom(n, t.child1); return} else if(!n.children.isEmpty) return
           case n@N_do_then_else(t)  => if (!message.excluded && message.child.template==t.child0 && !message.child.hasSuccess) {activateFrom(n, t.child2); return} else if(!n.children.isEmpty) return
           case _ => 
      }
      message.node.forEachParent(p => insertDeactivation(p,message.node))
      executeCodeIfDefined(message.node, message.node.onDeactivate)
      executeCodeIfDefined(message.node, message.node.onDeactivateOrSuspend)
      disconnect(childNode = message.node)
  }

  /*
   * Handle a success message
   * 
   * for n_ary and 1_ary nodes if the message comes from a child node:
   *   postpone further processing by inserting a continuation message 
   *   
   * for a script call node: transfer parameters
   * 
   * set the node's hadSuccess flag
   * execute "onSuccess" code, if defined
   * insert success messages for each parent node
   */
  def handleSuccess(message: Success): Unit = {
         // The following lines had been inserted on 10 April 2014 [c8f7a57], and outcommented on 22 April 2014.
         // These were wrong: a success message for a [while] would not be processed any more
         //if (message.node.hasSuccess) {
         //  return // should not occur?
         //}
         
         message.node match {
               case n@  N_annotation   (_  ) => {} // onSuccess?
                                           // Note: message.child!=null is needed because of doNeutral(n) in handleDeactivation()
               case n@  N_do_then      (t  ) => if (message.child!=null && message.child.template==t.child0) {activateFrom(n, t.child1); return}
               case n@  N_do_then_else (t  ) => if (                       message.child.template==t.child0) {activateFrom(n, t.child1); return}
               case n@  N_do_else      (t  ) => if (                       message.child.template==t.child0) {if (n.getLogicalKind_n_ary_op_ancestor==LogicalKind.Or) return}
               case n@  N_1_ary_op     (t  ) => if (message.child         != null) {insertContinuation1(message); return}
               case n@  N_n_ary_op     (_,_) => if (message.child         != null) {insertContinuation (message); return}
               case n@  N_launch_anchor(_  ) => if(n.nActivatedChildrenWithoutSuccess > 0) {return}
               case n@  N_call         (_  ) => if (!n.allActualParametersMatch) {return}
                                                n.transferParameters
               case _ =>
          }
         message.node.hasSuccess = true
         executeCodeIfDefined(message.node, message.node.onSuccess)
         message.node.forEachParent(p => insert(Success(p, message.node)))
  }
  /*
   * Handle an AAActivated message: activated atomic actions 
   * for n_ary and 1_ary nodes if the message comes from a child node:
   *   postpone further processing by inserting a continuation message 
   *   
   * insert AAActivated messages for each parent node
   */
  def handleAAActivated(message: AAActivated): Unit = {
          message.node match {
               case n@  N_1_ary_op      (t: T_1_ary        )  => if(message.child!=null) {
                                                                   insertContinuation1(message)
                                                                   //don't return; just put the continuations in place
                                                                 }
               case n@  N_n_ary_op      (_: T_n_ary, _     )  => if(message.child!=null) {
                                                                   if (n.indexChild_marksOptionalPart  >= 0 &&
                                                                       n.indexChild_marksOptionalPart < message.child.index)
                                                                     n.aaActivated_optional = true
                                                                   n.aaActivated = true
                                                                   insertContinuation(message)
                                                                   //don't return; just put the continuations in place
                                                                 }
               case _ => 
          }
          message.node.forEachParent(p => insert(AAActivated(p, message.node)))
  }
/*
  /*
   * Handle an CAActivated message: activated communications 
   * This may be of interest for a "+" operator higher up in the graph: 
   *   it may have to proceed with activating a next operand, 
   *   in case it had been "paused" by a optional break operand (. or ..)
   *
   * for n_ary and 1_ary nodes if the message comes from a child node:
   *   postpone further processing by inserting a continuation message 
   *   
   * insert CAActivated messages for each parent node
   */
  def handleCAActivated(message: CAActivated): Unit = {
          message.node match {
               case n@  N_1_ary_op      (t: T_1_ary        )  => if(message.child!=null) {
                                                                   insertContinuation1(message)
                                                                   //don't return; just put the continuations in place
                                                                 }
               case n@  N_n_ary_op      (_: T_n_ary, _     )  => if(message.child!=null) {
                                                                   insertContinuation(message)
                                                                   //don't return; just put the continuations in place
                                                                 }
               case _ => 
          }
          message.node.forEachParent(p => insert(CAActivated(p, message.node)))
  }
  
  /*
   * Communication handling features: still in the think&try phase
   * Not ready for testing
   */
  def handleCAActivatedTBD(message: CAActivatedTBD): Unit = {
    if (CommunicationMatchingMessage.activatedCommunicatorCalls.isEmpty) {
      insert(CommunicationMatchingMessage)
    }
    CommunicationMatchingMessage.activatedCommunicatorCalls += message.node
  }
  // TBD: process all fresh CA nodes to activate prospective communications
 def handleCommunicationMatchingMessage = {
    var startingCommunicationsOpenForMorePartners: List[N_communication] = Nil
    for (acc <- CommunicationMatchingMessage.activatedCommunicatorCalls) {
      // check out the associated communication relations:
      // if one of these may be activated with help of pending CA partners, then do so
      // else make this CA call pending as well
      
      var i = 0
      while (i < acc.communicator.roles.length && acc.children.isEmpty) {
        val cr = acc.communicator.roles(i)
        i += 1
        tryCommunication(acc, cr)
      }
      if (acc.children.isEmpty) {
        acc.communicator.instances += acc // TBD: remove again when acc is deactivated, using stopPending
      }
    }
    CommunicationMatchingMessage.activatedCommunicatorCalls.clear()
  }
        
  // a communication may become active when
  // all mandatory positions for partners at the same instance may be filled
  // partners should have compatible parameters, be active in parallel, and obey network topology
  def tryCommunication(freshCall: N_call, freshCallRole: CommunicatorRole): Boolean = {
    val communication = freshCallRole.communication
    
    def tryCommunicationWithPartners(partners: List[N_call]): Boolean = {
        def canCommunicateWithPartners(n: N_call): Boolean = {
          var i = 0
          while (i < partners.length) {
            // TBD: check for parallel locations
            val p = partners(i)
            val r = communication.communicatorRoles(i)
            // TBD: check parameter compatibilities
            
            // TBD: check network topology
          }
          return true
        }
      var i = partners.length // TBD: make it a List[List[N_call]]
        if (i == communication.communicatorRoles.length) {  
           val nc = N_communication(communication.template)
           // set nc.partners vv and make it activate
           nc.communication = communication
           nc.parents ++: partners
           for (p<-partners) {p addChild nc}
           //executeCode_call(nc);
           //activateFrom(nc, n.t_callee)}
           return true
        }
        else {
        val role = communication.communicatorRoles(i)
        val nodes = if (role==freshCallRole) List(freshCall)
                  else  role.communicator.instances
          var j = 0
          while (j < nodes.length) {
          val node = role.communicator.instances(j)
            j += 1
            if (canCommunicateWithPartners(node)) {
              if (tryCommunicationWithPartners(node::partners)) {
                return true;
              }
            }
          }
        return false
      }
    }
    // TBD: first try comms that may still grow (having multipicities other than One)
    return tryCommunicationWithPartners(Nil)
  }
*/          

  /*
   * Handle an AAHappened message
   *
   * Resets the node's hadSuccess flag
   * Increments the busyActions count
   * 
   * If the node is an n_ary or 1_ary operator: insert a continuation message 
   * If the node is a suspending operator: decide on what children to suspend
   * If the node is an exclusive opeator: decide on what children to exclude
   * 
   * Insert the exclude messages and suspend messages
   * For each parent node insert an AAHappened message
   * 
   * TBD: ensure that an n-ary node gets only 1 AAHappened msg 
   * after an AA started in a communication reachable from multiple child nodes (*)
   */
  def handleAAHappened(message: AAHappened): Unit = {
    message.node.hasSuccess = false
    message.node.numberOfBusyActions += (message.mode match {
      case     AtomicCodeFragmentExecuted =>  0
      case DurationalCodeFragmentStarted  =>  1
      case DurationalCodeFragmentEnded    => -1
    })
    message.node match {
       case n@N_1_ary_op(t: T_1_ary)    => insertContinuation1(message) //don't return; just put the continuations in place
       case n@N_n_ary_op(t: T_n_ary, _) => insertContinuation (message) //don't return; just put the continuations in place, mainly used for left merge operators
                                                                     
          // decide on exclusions and suspensions; deciding on exclusions must be done before activating next operands, of course
          var nodesToBeSuspended: Seq[n.Child] = null
          var nodesToBeExcluded : Seq[n.Child] = null
      if (T_n_ary_op.isSuspending(n.template)) {
          val s = message.child
          if (s.aaHappenedCount==1) {
            t.kind match {
              case "%&" | "%;"   => nodesToBeSuspended = n.children diff List(s)
              case "%"           => nodesToBeExcluded  = n.children.filter(_.index < s.index) 
                                    nodesToBeSuspended = n.children.filter(_.index > s.index)
              case "%/" | "%/%/" => nodesToBeSuspended = n.children.filter(_.index < s.index) 
            }
          }
      }
      else {
            t.kind match {
              case ";" | "|;" 
               | "||;" | "|;|" 
               | "+"   | "|+"  => nodesToBeExcluded = n.children.filter(_.index != message.child.index)
                             // after (*), do: nodesToBeExcluded = n.children -- message.aaHappeneds.map( (as:AAHappened) => as.child)  
                      
              case "/" | "|/" 
                 | "|/|"       => nodesToBeExcluded = n.children.filter(_.index < message.child.index)
                                  // after (*), do: 
                                  // val minIndex = message.child.index
                                  // nodesToBeExcluded = n.children -- message.aaHappeneds.map( (as:AAHappened) => as.child)
              case _ =>
            }
          }
        // do exclusions and suspensions
        if (nodesToBeExcluded !=null) nodesToBeExcluded .foreach((n) => insert(Exclude(message.node, n)))
        if (nodesToBeSuspended!=null) nodesToBeSuspended.foreach((n) => insert(Suspend(n)))
       case _ =>      
    }
    
    // message.child may be null now
    message.node.forEachParent(p => insert(AAHappened(p, message.node, message.mode)))
  }
  
  /*
   * Handle a break message (break  .   ..)
   * 
   * if the node is an n_ary operator:
   *   if the node is not already inactive, set its activation mode to the one specified by the break message
   *   insert a continuation message
   * else insert break messages for each parent node
   */
  def handleBreak(message: Break): Unit = {
      message.node match {
        case nn: N_n_ary_op =>
          if (nn.activationMode!=ActivationMode.Inactive) {
              nn.activationMode = message.activationMode
          }
          insertContinuation(message)
        case _ => message.node.forEachParent(p => insert(Break(p, message.node, message.activationMode)))
      }
  }
  
  /*
   * Handle an exclude message
   * 
   * Set the node's isExcluded flag
   * Interrupt asynchronously running code for the node, if any
   * 
   * If the node is a communication partner: make it stop pending (TBD)
   * If the node is an atomic action: remove AAToBeExecuted message, if any 
   *         (TBD: also remove AAToBeReExecuted message, if any?)
   *         inset a deactivation message
   * insert exclude messages for each child node
   */
  def handleExclude(message: Exclude): Unit = { // TBD: remove messages for the node; interrupt execution
    val n = message.node
    n.isExcluded = true
    
    if (message.node.template.isInstanceOf[TemplateCodeHolder[_,_]] && message.node.codeExecutor != null)
      message.node.codeExecutor.interruptAA
    
    n match {
      case cc: N_call[_] => cc.stopPending
      case aa: N_code_fragment[_] =>
        aa.codeExecutor.cancelAA
        if (aa.msgAAToBeExecuted != null) {
          remove(message) // does not really remove from the queue; will have to check the canceled flag of the codeExecutor...
          aa.msgAAToBeExecuted = null
        }
        // TBD: also for caNodes!!
        insert(Deactivation(aa, null, excluded=true))
      case _ =>
    }
    
    n.children.foreach {c => insert(Exclude(n,c))}
  }
  
  /*
   * Handle a continuation message for an unary node
   */
  def handleContinuation1(message: Continuation1): Unit = {
    val n = message.node.asInstanceOf[N_1_ary_op]
    n.continuation = null
    // TBD
  }
  
  /*
   * Handle an AAToBeExecuted message
   * 
   * perform the codeExecutor's executeAA method
   * 
   * Note: the message may have been canceled instead of removed from the queue (was easier to implement),
   * so for the time being check the canceled flag
   */
  def handleAAToBeExecuted[T<:TemplateCodeHolder[R,_],R](message: AAToBeExecuted[R]) {
    val e = message.node.codeExecutor
    if (!e.canceled)  // temporary fix, since the message queue does not yet allow for removals
         e.executeAA
  }
  /*
   * Handle an AAToBeReexecuted message
   * 
   * insert an AAToBeExecuted message
   * 
   * Note: the message may have been canceled instead of removed from the queue (was easier to implement),
   * so for the time being check the canceled flag
   */
  def handleAAToBeReexecuted[T<:TemplateCodeHolder[R,_],R](message: AAToBeReexecuted[R]) {
    val e = message.node.codeExecutor
    if (!e.canceled) // temporary fix, since the message queue does not yet allow for removals
       insert(AAToBeExecuted(message.node)) // this way, failed {??} code ends up at the back of the queue
  }
  /*
   * Handle an AAExecutionFinished message
   * 
   * perform the codeExecutor's afterExecuteAA method,
   * which may insert success and deactivation messages in turn
   * 
   * Note:
   * A node's code executor has just finished execution. This may have been done asynchronously.
   * It has inserted an AAExecutionFinished, so that this will be handled synchronously in the main script executor loop.
   *
   */
  def handleAAExecutionFinished[T<:TemplateCodeHolder[R,_],R](message: AAExecutionFinished) {
     message.node.codeExecutor.afterExecuteAA
  }
  
  /*
   * handleContinuation:
   * 
   * The most complicated method of the Script Executor: 
   * determine what an N-ary operator will do
   * after it has received a set of messages. Potential outcomes include:
   * - activate next operand and/or have success
   * - suspend, resume, exclude
   * - deactivate
   * - nothing
   *   
   * The decision is based on three aspects:
   * - the kind of operator
   * - the state of the node
   * - the received messages
  */ 
  def handleContinuation(message: Continuation): Unit = {
    val n = message.node.asInstanceOf[N_n_ary_op]
    n.continuation = null
    
    // decide on what to do: 
    // activate next operand and/or have success, suspend, resume, exclude, or deactivate or nothing
    
    // decide on activate next operand
    
    var activateNextOrEnded       = false
    var activateNext              = false
    var activationEnded           = false
    var activationEndedOptionally = false
    var childNode: CallGraphNode = null // may indicate node from which the a message came

    var shouldSucceed = false    
    
    val isSequential = 
       n.template.kind match {
        case ";" | "|;"  | "||;" |  "|;|" => true
        case _ => false
       }
    
    if (isSequential) {
      
       val s = message.success
       val b = message.break
       if (b!=null) {activateNextOrEnded = true; childNode = b.child
                     if (b.activationMode==ActivationMode.Optional) {
                       activationEndedOptionally = true
                     }
                     else n.mustBreak
                    }
       if (s!=null) {activateNextOrEnded = true; childNode = s.child}
    }
    else
    {
     if (n.activationMode!=ActivationMode.Inactive) {
       n.template.kind match {
//      case "%" => val d = message.deactivations; 
//                  val b = message.break
//                  if (d!=Nil) {
//                    activateNextOrEnded = d.size>0 && !d.head.excluded
//                    if (activateNextOrEnded) {
//                      childNode = d.head.node
//                    }
//                  }
         
      case "+" | "|+" | "|+|" // "+" node activations may be broken by "." if no atomic actions had been activated
                      => val a = message.aaActivated; val c = message.caActivated; val b = message.break
                         activateNextOrEnded = if (b==null) true
                                               else if (b.activationMode==ActivationMode.Optional) a!=null || c!=null
                                               else false 
                         if (activateNextOrEnded) {
                           childNode = n.lastActivatedChild         
                           //childNode = message.childNode         

                         }
                  
      case kind if (T_n_ary_op.isLeftMerge(kind)) => 
                         val aa = message.aaActivated
                         val ca = message.caActivated
                         val as = message.aaHappeneds
                         val b  = message.break
                         activateNextOrEnded = aa==null && ca==null ||
                                               as!=Nil  && as.exists( (as:AAHappened) => as.node==n.lastActivatedChild )
                         if (b!=null) {
                           // ???
                         }
                         if (activateNextOrEnded) {
                           childNode = n.lastActivatedChild
                         }
      
      /*
       *       . / a     => no pause; a is optional
       * (-) / . / a     => no pause; a is optional
       *  a  / . / b     => pause; after a happens / is done
       */
      case "/" | "|/"  | "|/|" if n.indexChild_marksPause >= 0 && message.aaHappeneds!=Nil => 
                         if (message.aaHappeneds.exists(a=>a.node.index > n.indexChild_marksOptionalPart) && message.deactivations==Nil) {
                           activateNextOrEnded = true
                           n.activationMode = ActivationMode.Active
                           n.resetNActivatedOptionalChildren
                           n.indexChild_marksOptionalPart = n.indexChild_marksPause
                           n.indexChild_marksPause        = -1
                           n.aaActivated_optional         = false
                           childNode = n.lastActivatedChild
                         }
                         
      /*
       *       . & a     => no pause; a is optional
       * (+) & . & a     => no pause; a is optional
       *  a  & . & b     => pause; after a happens b is activated as optional
       */
      case _ if n.indexChild_marksPause >= 0 && message.aaHappeneds!=Nil && message.aaHappeneds.exists(a=>a.child.index > n.indexChild_marksOptionalPart) => 
                           if (doTrace) traceAttributes(n, "A")

                           activateNextOrEnded = true
                           n.activationMode = ActivationMode.Active
                           n.resetNActivatedOptionalChildren
                           n.indexChild_marksOptionalPart = n.indexChild_marksPause
                           n.indexChild_marksPause        = -1
                           n.aaActivated_optional         = false
                           childNode = n.lastActivatedChild

      case _ if n.indexChild_marksOptionalPart >= 0 && message.aaHappeneds!=Nil && message.aaHappeneds.exists(a=>a.child.index > n.indexChild_marksOptionalPart) => 
                           if (doTrace) traceAttributes(n, "B")
                           activateNextOrEnded = true
                           n.activationMode = ActivationMode.Active
                           n.resetNActivatedOptionalChildren
                           n.indexChild_marksOptionalPart = n.indexChild_marksPause
                           n.indexChild_marksPause        = -1
                           n.aaActivated_optional         = false
                           childNode = n.lastActivatedChild
                         
       case _  =>        val b = message.break
                         if (b==null) {
                           if (message.aaHappeneds != Nil || message.activation != null) {
                             if (doTrace) traceAttributes(n, "C")
                             activateNextOrEnded = true
                             childNode = n.lastActivatedChild
                           }
                           else if (doTrace) traceAttributes(n, "D")

                         } 
                         else if (b.activationMode==ActivationMode.Optional) {
                           if (n.aaActivated_optional) { 
                             if (doTrace) traceAttributes(n, "E")
                             activateNextOrEnded = true
                             n.activationMode = ActivationMode.Active
                             n.resetNActivatedOptionalChildren
                             n.indexChild_marksOptionalPart = n.indexChild_marksPause
                             n.indexChild_marksPause        = -1
                             n.aaActivated_optional         = false
                             childNode = n.lastActivatedChild
                           }
                           else if (message.aaActivated != null
                                ||  n.indexChild_marksOptionalPart < 0 && n.aaActivated){ // TBD: possibly wrong test; 
                                                          // we should ask whether any AA had been activated in the part before "."
                             if (doTrace) traceAttributes(n, "F")
                             n.activationMode = ActivationMode.Optional // TBD: may possibly be dropped???; check n.indexChild_marksPause >= 0
                             n.indexChild_marksPause = b.child.index
                           }
                           else {
                             if (doTrace) traceAttributes(n, "G")
                             activateNextOrEnded = true
                             n.activationMode = ActivationMode.Optional
                             n.resetNActivatedOptionalChildren
                             n.indexChild_marksOptionalPart = b.child.index
                             n.indexChild_marksPause        = -1
                             childNode = n.lastActivatedChild
                           }
                         }
       }
     }
    }

    var nextActivationTemplateIndex = 0
  var nextActivationPass = 0
  if (activateNextOrEnded) {    
    // old: childNode = if (T_n_ary.isLeftMerge(n.template.kind)) n.lastActivatedChild else message.childNode ; now done before
    nextActivationTemplateIndex = childNode.template.indexAsChild+1
    nextActivationPass = childNode.pass 
    
    message.node.activationMode = ActivationMode.Active
    
    // ??? is this right ???
    def actNext = !(activationEnded || activationEndedOptionally)
    if (n.hadFullBreak) activationEnded = true
    else if (nextActivationTemplateIndex==message.node.template.children.size) {
      if (message.node.isIteration) {
        nextActivationTemplateIndex = 0
        nextActivationPass += 1
        activateNext = actNext
      }
      else {
        activationEnded = true
      }
    }
    else {
      activateNext = actNext
    }  
    }
    
    // decide on exclusions and suspensions; deciding on exclusions must be done before activating next operands, of course
    var nodesToBeExcluded : Seq[CallGraphNode.Child] = null
    var nodesToBeSuspended: Seq[CallGraphNode.Child] = null
    n.template.kind match {

      case "/" | "|/" 
        | "|/|"        => // deactivate to the right when one has finished successfully
                      // TBD: something goes wrong here; LookupFrame2 does not "recover" from a Cancel search
                          message.deactivations match {
                            case d::tail => if (d.child.hasSuccess && !d.excluded) {
                              nodesToBeExcluded = n.children.filter(_.index>d.child.index)
                            }
                            case _ =>
                          }
                  
      case "&&"  | "||" 
         | "&&:" | "||:" => val isLogicalOr = T_n_ary_op.getLogicalKind(n.template.kind)==LogicalKind.Or
                            // TBD: better descriptive name for consideredNodes
                            val consideredNodes = message.deactivations.map(_.child).filter(
                               (c: CallGraphNode) => c.hasSuccess==isLogicalOr)
                            if (!consideredNodes.isEmpty) {
                              nodesToBeExcluded = n.children diff consideredNodes
                              activateNext = false
                            }
      case _ =>          
    }
    // decide further on success and resumptions
    if (!shouldSucceed && !n.hasSuccess) { // could already have been set for .. as child of ;
      
      // TBD: improve
      //var nodesToBeResumed: Buffer[CallGraphNode] = null
      //if (message.success != null || message.aaHappeneds != Nil) {
      n.template.kind match {
            case ";" => shouldSucceed = activationEnded || activationEndedOptionally
            case "/" => shouldSucceed = message.success != null ||
                                        message.aaHappeneds.exists(_.child.index<n.rightmostChildThatEndedInSuccess_index) || 
                                    n.nActivatedChildrenWithSuccess > 0
            case _ =>
              T_n_ary_op.getLogicalKind(n.template.kind) match {
                case LogicalKind.None =>
                case LogicalKind.And  => shouldSucceed = !activateNext &&
                                                         n.nActivatedMandatoryChildrenWithoutSuccess == 0
                case LogicalKind.Or   => shouldSucceed = n.nActivatedChildrenWithSuccess > 0
                  }
      }
  }
    if (doTrace) {
      traceAttributes(n, "Finally")
      traceAttribute("activateNext", activateNext)
      traceAttribute("activationEnded", activationEnded)
      traceAttribute("activationEndedOptionally", activationEndedOptionally)
      traceAttribute("shouldSucceed", shouldSucceed)
    }
    if (shouldSucceed) {
      insert(Success(n))   // TBD: prevent multiple successes at same "time"
    }
    // do exclusions and suspensions
    if (nodesToBeExcluded !=null) nodesToBeExcluded .foreach((n) => insert(Exclude(message.node,n)))
    if (nodesToBeSuspended!=null) nodesToBeSuspended.foreach((n) => insert(Suspend(n)))

    // do activation    
    if (isSequential) activateNext = activateNext && n.children.isEmpty
    if (activateNext) {
      val t = message.node.template.children(nextActivationTemplateIndex)
      activateFrom(message.node, t, Some(nextActivationPass))
      val activation = if (message.activation != null) message.activation else Activation(message.node)
      
      val nary_op_isLeftMerge = n match {
        case nary@N_n_ary_op (t: T_n_ary, isLeftMerge) => isLeftMerge case _ => false
      }
      if (!nary_op_isLeftMerge) insertContinuation(activation, n)
    }
    else if (n.children.isEmpty) {
      insertDeactivation(n, null)
    }
      
    // decide on deactivation of n
    
  }
    
  val defaultHandler: MessageHandler = {
      case a@ Activation        (_) => handleActivation   (a)
      case a@Continuation       (_) => handleContinuation (a)
      case a@Continuation1      (_) => handleContinuation1(a)
      case a@Deactivation  (_,_, _) => handleDeactivation (a)
      case a@Suspend            (_) => {}
      case a@Resume             (_) => {}
      case a@Exclude          (_,_) => handleExclude    (a)
      case a@Success          (_,_) => handleSuccess    (a)
      case a@Break        (_, _, _) => handleBreak      (a)
      case a@AAActivated      (_,_) => handleAAActivated(a)
   // case a@CAActivated      (_,_) => handleCAActivated(a)
   // case a@CAActivatedTBD     (_) => handleCAActivatedTBD(a)
      case a@AAHappened     (_,_,_) => handleAAHappened (a)
      case a@AAExecutionFinished(_) => handleAAExecutionFinished(a)
      case a@AAToBeReexecuted   (_) => handleAAToBeReexecuted   (a)
      case a@AAToBeExecuted     (_) => handleAAToBeExecuted     (a)
   // case CommunicationMatchingMessage => handleCommunicationMatchingMessage
    }
  val communicationHandler: MessageHandler = {
    case InvokeFromET(_, payload) => payload()
  }  
}