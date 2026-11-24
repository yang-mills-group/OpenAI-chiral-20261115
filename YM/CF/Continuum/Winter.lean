/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Continuum.TagMirror
import YM.Push.LOCAL_SPLITTING.Transport
import YM.CF.Hom.Sally
import YM.CF.Hive.Hen

/-!
# Mirrors and relative FiniteGaugeData density

Account for the a.e. tag condition in the transport of the effective data.
These statements use the *unsquared* FiniteGaugeData ket formula, except the overall
scalar exp(v) has been removed (so to normalize this version divide by
Graph's corresponding relative denominator, exp(-v) times partition).
Not a reflection *positivity* theorem; conjugation only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {m B N L : Side} {U Ω : UNI (Single N)} {x y z η : ℝ}
local notation "Λ" => CSide m B
section fuel
variable {P : BudgetPoint} {Q : Sweep N → Prop} (s : Sweep N) {F G : RegBudget N}
  {H : ForceBudget N} (a : IncX Q F P x y) (hQ : Q s) {u : UNI SpinIdx} (w : JetS s.s s.charge (detX s.s) u)
set_option quotPrecheck false
local notation "Πd" => paintR s.charge (detX s.s) (prepU (castX s) u (xtra s.charge) N)
private abbrev moveV (s:Sweep N)(x:Support (More N)):=x.map (boxA s).symm.toEmbedding
private lemma tolerance(X:Support (More N))(V:Pane N)(t:ℝ) : pingS t X V ↔ ∃ e, e<t ∧ Healthy e X V:=by
  classical
  constructor; swap; · rintro ⟨e,v,q⟩; exact ping_lo v q
  intro p; let S:=univ.filter fun i:Face (Per (More N))=> ¬Disjoint X (touched i); let k(i:Face (Per (More N))):= SU.group.chord (faceValue V i)
  have he : ∃ e, e<t ∧ ∀ i∈S, k i<e:=by
    by_cases h:S.Nonempty; swap; · exact ⟨t-1,by linarith,fun i u=>(h ⟨i,u⟩).elim⟩
    obtain ⟨b,u,hb⟩:= exists_between ((sup'_lt_iff ..).mpr (fun i e=> p i (mem_filter.mp e).2) : S.sup' h k<t)
    exact ⟨b,hb,fun i e=> lt_of_le_of_lt (le_sup' k e) u⟩
  obtain ⟨b,g,hq⟩:=he; exact ⟨b,g, ping_le (fun i e=>hq i (mem_filter.mpr ⟨mem_univ _,e⟩))⟩
private lemma warm_move (t:ℝ)(X:Support (More N))(V:Pane N): pingS t (moveV s X) (flashA s V) ↔ pingS t X V:=by
  rw [tolerance,tolerance]; unfold Healthy; simp_rw [flagsA]; refine exists_congr fun b=>and_congr_right fun _=>Finset.disjoint_map _
-- rework elementary action lemma from Haro/Salt
private lemma hub_injective : Injective (moveHub s):=by
 intro i j h; apply Subtype.ext; have ht:=congrArg Subtype.val h; refine Prod.ext ((boxA s).symm.injective (congr_arg Prod.fst ht)) ?_; exact Finset.map_injective (boxA s).symm.toEmbedding (congrArg Prod.snd ht)
private lemma force_injective : Injective (moveForce s) := by
 intro i j h; apply Subtype.ext; have ht:=congrArg Subtype.val h; exact Prod.ext (hub_injective s (congrArg Prod.fst ht)) (Finset.map_injective _ (congr_arg Prod.snd ht))
private abbrev forcePerm := Equiv.ofBijective (moveForce s) ⟨force_injective s, Finite.surjective_of_injective (force_injective s)⟩
include a hQ w

lemma turn_exponent (V : Pane N) : exponentL P F (flashA s V) = Πd (exponentL P F V) := by
  classical
  let E:= Equiv.ofBijective (moveHub s) ⟨hub_injective s, Finite.surjective_of_injective (hub_injective s)⟩
  symm; unfold exponentL; rw [map_sum]; refine sum_equiv E (fun i=> by simp) (fun i _=>?_)
  have he : (E i).val.2=moveV s i.val.2:= rfl
  unfold numbE; rw [he]; by_cases k:pingS P.threshold i.val.2 V
  · rw [Set.indicator_of_mem (show V∈_ from k), Set.indicator_of_mem (show flashA s V∈_ from (warm_move ..).mpr k)]; exact (a.face s hQ u w i V).symm
  rw [Set.indicator_of_notMem (show V∉_ from k), Set.indicator_of_notMem (show flashA s V∉_ from mt (warm_move ..).mp k), map_zero]
omit a hQ w
set_option quotPrecheck false
local notation "Ωp" => forcePerm s
private lemma force_sets (X : Finset (Force N)) (V : Pane N) : coverF P ((forcePerm s).finsetCongr X) (flashA s V) ↔ coverF P X V := by
  classical
  have he : (((forcePerm s).finsetCongr X).biUnion (fun i=>i.val.2))=moveV s (X.biUnion (fun i=>i.val.2)):= by
    change (X.map _).biUnion _= _; ext j; unfold moveV
    constructor
    · intro p; obtain ⟨j',u,r⟩:=mem_biUnion.mp p; obtain ⟨v,q,rfl⟩:=mem_map.mp u; obtain ⟨x,h,rfl⟩:=mem_map.mp (show j∈moveV s v.val.2 from r); exact mem_map_of_mem _ (mem_biUnion.mpr ⟨v,q,h⟩)
    intro p; obtain ⟨v,q,rfl⟩:= mem_map.mp p; obtain ⟨i,h,hq⟩:=mem_biUnion.mp q; exact mem_biUnion.mpr ⟨moveForce s i, mem_map.mpr ⟨i,h,rfl⟩, mem_map_of_mem _ hq⟩
  unfold coverF; rw [he,flagsA]; exact (Finset.map_injective _).eq_iff
private lemma force_pairwise (X : Finset (Force N)) : Set.PairwiseDisjoint ((forcePerm s).finsetCongr X:Set (Force N)) (fun i=>i.val.1.val.2) ↔ Set.PairwiseDisjoint (X:Set (Force N)) (fun i=>i.val.1.val.2) := by
  classical
  let T (i:Force N):=i.val.1.val.2
  have hb(i j:Force N): Disjoint (T ((forcePerm s) i)) (T ((forcePerm s) j)) ↔ Disjoint (T i) (T j) := Finset.disjoint_map _
  constructor
  · intro D i hi j hj h; exact hb i j|>.mp ((@D ((forcePerm s) i) (mem_map_of_mem _ hi) ((forcePerm s) j) (mem_map_of_mem _ hj) ((forcePerm s).injective.ne h)))
  intro D i hi j hj h; obtain ⟨i,ui,rfl⟩:= mem_map.mp hi; obtain ⟨j,uj,rfl⟩:= mem_map.mp hj
  exact hb i j|>.mpr ((@D i ui j uj (fun q=> h (congrArg (forcePerm s) q))))

include hQ w
lemma turn_forced (b : Dark Q H P x y) (V : Pane N) (J : Ids N) (hi : Injective (priorP J)) : fueled P H (flashA s V, bun s J) = Πd (fueled P H (V,J)) := by
  classical
  have hc(k:Force N): clamp P ((forcePerm s) k) (H ((forcePerm s) k)) (flashA s V,bun s J) = Πd (clamp P k (H k) (V,J)):= by
    have he : boundF ((forcePerm s) k) P (flashA s V) ↔ boundF k P V:= by
      change pingS _ (moveV s k.val.1.val.2 \ moveV s k.val.2) _ ↔ _; rw [←Finset.map_sdiff]; exact warm_move ..
    unfold clamp; dsimp only; rw [he]; split_ifs with g
    · exact b.face s hQ u w k V J hi
    exact Eq.symm (map_zero _)
  symm; unfold fueled; rw [map_sum]; refine sum_equiv (forcePerm s).finsetCongr (fun i=>by simp) (fun i _=>?_)
  dsimp only; have hiff:= (and_congr (force_sets (P:=P) s i V) (force_pairwise s i)); by_cases t:coverF P i V ∧ Set.PairwiseDisjoint (i:Set (Force N)) (fun x=>x.val.1.val.2); swap
  · rw [if_neg t, if_neg (mt hiff.mp t),map_zero]
  rw [if_pos t, if_pos (hiff.mpr t), map_prod]; change _=∏ j∈i.map (forcePerm s).toEmbedding, _; rw [prod_map]; exact prod_congr rfl fun j _=>(hc j).symm
omit w hQ
end fuel
section amplitude
variable {e v a η r C : ℝ} {j n : ℕ} {hj : Odd L.val}{Y : Pricing j L hj (Thread j)}
  {P : Grasp Y B e} {X : GramM (CSide m B)} {K : Scree.Loom (CSide m B)}
variable (C' : Hom.Credit)
lemma density_turn (t : Hom.InterestX C' Λ X.J) (h0 : 1 ≤ j) (D : Pearl P) (F : Stamped j L hj Y)
  (H0 : Roof Λ v e n K) (F1 : IncX (fun _ => True) X.F X.p x y) (F2 : IncX (fun _ => True) X.slip X.p x z) (Fx : Dark (fun _ => True) X.K X.p x η) (i : Axis) (V : Orbit Λ) (hV : Injective (priorP V.2)) (hp : P.roundZ ≤ (CSide m B).val) :
    arum (fullTurn m B i) false true (mateK Λ) (Complex.exp (-X.v) • denZ X P K V)=Complex.exp (-X.v) • denZ X P K (reflectedOrbitFun m B i V) := by
  let T:=fullTurn m B i
  let W:=sweep Λ i
  let R:= GramM.board X
  let J:=reflectedOrbitFun m B i V
  let Z:=K V
  have hw : detX W.s=true:=Spire.det_t i
  have hu : detX (shape i).s=true:=Spire.det_t i
  have hh : JetS W.s W.charge (detX W.s) (pinLift i):= by rw [hw]; exact mirrorX i
  have hZ:K J=flashA W Z:=H0.move _ _ _ hV
  have hv: Guard Z e:= H0.paid V
  have hQ: flashA W Z=stir inert (shape i) Z:=flip_shapes i Z
  have h2: Pec.pigment X.J.I (flashA W Z)=star (Pec.pigment X.J.I Z) := by
    rw [hQ]; change Pec.lexn _ (Yg (incX (Signed.mirror _)) _) = _; rw [Pec.prog,Pec.complX,Spire.det_t]; rfl
  have h3 : X.path.inChannels X.funds X.p X.beta J.1=X.path.inChannels X.funds X.p X.beta V.1:= by
    change X.path.inChannels _ _ _ (flashA W V.1)=_; rw [reflected_first,mirrorPane_eq]; exact YM.Push.Local.channels_pull ..
  let NL:= X.betaL K V-X.v; let NL':= X.betaL K J-X.v
  have hf : NL'=star NL := by unfold NL' NL GramM.betaL GramM.H0; rw [h3,hZ,h2]; simp; ring_nf; rfl
  let A:=spar j X.J.M Z; let B':=spar j X.J.M (flashA W Z); have hA : IsStarProjection A:= (P.broadness _ hp X.J.M).projection _ hv
  have hB : IsStarProjection B':= (P.broadness _ hp X.J.M).projection _ (hZ ▸ H0.paid J)
  let L' := paintR false true T
  have ht : L' (R V) = R J:=by
    have hx:= turn_exponent W F1 (by trivial) hh V.1
    have hy:= turn_exponent W F2 (by trivial) hh V.1
    have hz:= turn_forced W (by trivial) hh Fx V.1 V.2 hV
    rw [hw] at hx hy hz; unfold R GramM.board
    letI : NormedAlgebra ℚ (Scree.Cipher Λ):= NormedAlgebra.restrictScalars ℚ ℝ _
    rw [map_mul,map_exp L' L'.toLinearMap.continuous_of_finiteDimensional,map_add]; have hp' : prepU (castX W) (pinLift i) (xtra W.charge) Λ=T:=tilt_prep i
    rw [hp'] at hx hy hz; exact congrArg₂ (·*·) (congrArg exp (congrArg₂ (·+·) hx.symm hy.symm)) hz.symm
  have h4: sings false T A= swapX true B':= by
    unfold A B'; rw [hQ]; exact funde_f (shape i) inert (pinLift i) (mirrorX i) Z j h0 X.J.M _ (F.fields_one _ (P.needed.trans hp)) (hv.shrink P.gem)
  have h5: tourP T false true (tank A (R V))=tank B' (R J):=by rw [←ht,tank_eq _ _ hA,tank_eq _ _ hB]; exact appleT hA hB _ _ _ h4 _
  have he(M : Orbit Λ): Complex.exp (-X.v) • denZ X P K M=Complex.exp (X.betaL K M-X.v) • acts (tank (spar j X.J.M (K M)) (R M)) (relV P X.J (K M)) :=by
    unfold denZ; rw [smul_smul,←Complex.exp_add]; congr 2; ring_nf
  change arum T _ _ _ _=_
  rw [he,he,arum_scale,show X.betaL K J-X.v= _ from hf,hZ, arum_act,h5]
  have hx : arum T false true (mateK Λ) (relV P X.J Z)= relV P X.J (flashA W Z):= by
    let Y':= Hive.birds false D F hp h0 (shape i) (pinLift i) hh X.J.P t.leanJ.1 t.ready Z hv (M:=X.J.M)
    rw [hu] at Y'; rw [hQ]; exact Y'
  rw [hx]; congr 1; exact Eq.symm (Complex.exp_conj _)
end amplitude
end YM.CF.Window
