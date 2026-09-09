From LessThanOneAPress.Proofs Require Import
  GameTypes InputSemantics CleanEntry ClightRefinement FirstTargetRefinement.

(** A progress-tracking interface for the existing conditional impossibility
    proof.  Each field is still an obligation about the SAME run, certificate,
    and route trace.  Naming the fields proves none of them.  In particular,
    a local source theorem or a finite receipt cannot inhabit a field without
    its live-execution coverage argument.

    The equivalence below checks that this decomposition neither drops a
    surviving class nor changes the old closure obligation.  Already proved
    certified-semantics exclusions remain consumed in FirstTargetRefinement;
    they are not requested again as fields here. *)
Definition NoAConcreteWriterClassUnreachableObligation
    (projection : ClightObservationProjection)
    (class : ConcreteBypassClass) : Prop :=
  forall run initial
      (certificate : ClightFrameRefinementCertificate projection run initial)
      trace,
    CleanPyramidEntry initial ->
    ClightRouteTraceProjection projection run initial certificate trace ->
    EvidenceBearingFirstTargetCutClassification
      projection run initial certificate trace ->
    fewer_than_one_a_press (project_inputs projection run) ->
    forall entrance region target_frame target_observation,
      ~ EvidenceBearingBypassAt projection run initial certificate trace
          entrance class region target_frame target_observation.

Record RemainingNoAWriterObligations
    (projection : ClightObservationProjection) : Prop := {
  remaining_ordinary_motion :
    NoAConcreteWriterClassUnreachableObligation projection
      BypassOrdinaryMarioMotionOrStaticGeometry;
  remaining_platform_displacement :
    NoAConcreteWriterClassUnreachableObligation projection
      BypassPlatformDisplacement;
  remaining_object_push :
    NoAConcreteWriterClassUnreachableObligation projection
      BypassObjectPushOrMovingGeometry;
  remaining_collision_clip :
    NoAConcreteWriterClassUnreachableObligation projection
      BypassCollisionClipOrTunnel;
  remaining_coordinate_alias :
    NoAConcreteWriterClassUnreachableObligation projection
      BypassParallelUniverseOrOutOfBounds;
  remaining_lifecycle_displacement :
    NoAConcreteWriterClassUnreachableObligation projection
      BypassMacroOrLifecycleAnomaly
}.

(** The legacy coordinate-class name is not a machine-semantics extension.
    Its evidence is still restricted to the selected Clight model. *)
Theorem remaining_no_a_writer_obligations_suffice :
  forall projection,
    RemainingNoAWriterObligations projection ->
    NoAOpenRouteWriterClassesUnreachableObligation projection.
Proof.
  intros projection [Hmotion Hplatform Hobject Hclip Halias Hlifecycle]
    run initial certificate trace Hclean Hroute Hclassify Hnoa
    entrance class region target_frame target_observation Hclass.
  destruct Hclass as [Heq | [Heq | [Heq | [Heq | [Heq | Heq]]]]];
    subst class.
  - exact (Hmotion run initial certificate trace Hclean Hroute Hclassify Hnoa
      entrance region target_frame target_observation).
  - exact (Hplatform run initial certificate trace Hclean Hroute Hclassify Hnoa
      entrance region target_frame target_observation).
  - exact (Hobject run initial certificate trace Hclean Hroute Hclassify Hnoa
      entrance region target_frame target_observation).
  - exact (Hclip run initial certificate trace Hclean Hroute Hclassify Hnoa
      entrance region target_frame target_observation).
  - exact (Halias run initial certificate trace Hclean Hroute Hclassify Hnoa
      entrance region target_frame target_observation).
  - exact (Hlifecycle run initial certificate trace Hclean Hroute Hclassify Hnoa
      entrance region target_frame target_observation).
Qed.

Theorem remaining_no_a_writer_obligations_equivalent :
  forall projection,
    RemainingNoAWriterObligations projection <->
    NoAOpenRouteWriterClassesUnreachableObligation projection.
Proof.
  intro projection. split.
  - exact (remaining_no_a_writer_obligations_suffice projection).
  - intro Hclosed. constructor;
      intros run initial certificate trace Hclean Hroute Hclassify Hnoa
        entrance region target_frame target_observation;
      eapply (Hclosed run initial certificate trace Hclean Hroute Hclassify Hnoa
        entrance _ region target_frame target_observation);
      tauto.
Qed.
