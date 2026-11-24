import GaugeFieldConstruction.Artemis4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I θ E:Type}[Fintype I][LinearOrder I]{n:Side}
open Rio Grotto Isle
-- Loans trajectory only intended intersection hypotheses.These imply precisely for every such selection. From base.Xu
section
variable (σ:I→ Seat n) (F:XE I (InkD n) n)(K:KK I (Copy n) n)(T: PI I n→ℝ)(Y:KI I n→ℝ)(μ:I→ℝ)(s:I→List I)(G:I→Hub n)
variable (C:BudgetPoint)(h ℓ Ω η a:ℝ)(b k:ℕ)(fV:BillX C σ h 1 T F)(tV:BillF C σ h 1 k Y K)
structure Things (L:List I):Prop where
    face (i:I)(t:i∈L): BlankM F K i
    proc (i:I)(t:i∈L):i ∉ s i
    noble:L.Nodup
    womb(i:I)(t:i∈L): (s i).length≤2 ∧ ψS σ (s i) ∧ poke_F σ (G i).val.2 (s i).toFinset
abbrev ΓNow (P: Rio I n)(x:Key I):=Canz σ _ (RX F P) x
abbrev ΦNow(P:Rio I n)(x:Key I):= Canz σ _ (BX K P) x
def quakeY(L: List I)(U:Orbit n):Key I→Cipher n:= sayQ C U (ΓNow σ F (ProgramL σ F K μ s G L)) (ΦNow σ K (ProgramL σ F K μ s G L))
-- Trees costs in statement. right eta update.Vect.Scope every f.Range.
variable (v:0≤h)(q:Cube_M b*Ω≤1)
local notation "Gm"=> quakeY σ F K μ s G C
local notation "ηL"=> rental b a η T Y
section
variable (U:Orbit n)(d:Rue.FleetS C.threshold U.1)
variable (i:I)(p:Hub n)(S:List I)(x:ℝ)
-- Note River for every evaluated Mark before E cut.
include d
lemma say_r (A:Rio I n): River (sayQ C U (ΓNow σ F A) (ΦNow σ K A)):=by -- dummy binder remove. q.C. needs Fleet. true for all anyway.hum
 let X:= fun z:Key I=> exponentL C (ΓNow σ F A z) U.1
 let V:=fun i:Force n=> fun z:Key I=>ΦNow σ K A z i U
 have hK(i):River (V i):=by unfold V ΦNow Canz; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact (tip_bank _ _ (fun j _=>lift_b j _)).1
 have hx: River X:=by
    unfold X exponentL; apply (tip_bank _ _ _).1; intro i _; by_cases h:pingS C.threshold i.val.2 U.1; swap; · unfold numbE; simp_rw[Set.indicator_of_notMem (s:={t|pingS C.threshold i.val.2 t}) (a:=U.1) h]; exact zeroR _
    unfold numbE; simp_rw [Set.indicator_of_mem (s:={t|pingS C.threshold i.val.2 t}) h]; unfold ΓNow Canz; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact (tip_bank _ _ (fun j _=>lift_b j _)).1
 unfold sayQ; simp_rw [hum_pay d] -- tune replace
 apply River.mul_T hx.exp_V; unfold hum; apply (tip_bank _ _ _).1; intro i hi; clear hi; induction i using Finset.induction_on with
 | empty=> simp_rw [prod_empty]; exact zeroR _
 | insert j t p ih=> simp_rw[prod_insert p]; exact (hK j).mul_T ih
omit d in
private lemma blank_C (i:I){α:Type}[Fintype α]{M:Type}[AddCommMonoid M][Module ℂ M](P:dues I α→ M)(W:∀ x,P x≠0 → i∉x.1)(j:α)(x:Key I):Canz σ _ P (dune i x) j=Canz σ _ P x j:=by
 unfold Canz; apply Finset.sum_congr rfl; intro V h; by_cases p:P (V,j)=0; · rw [p,smul_zero,smul_zero]
 apply congrArg (fun i:ℂ=> i • _); apply pine_e i; exact fun k t=> update_of_ne (fun q:k=i=> W (V,j) p (q ▸ t)) ..
section
variable (L M:List I)(P:Rio I n)(W:CashI I n)(t:Weighted C σ 1 h k P W)
local notation "K0"=> FrameT (RX F P) (BX K P)
include fV tV t d
private lemma Lprep (w:σ i=p.val.1)(c:Things σ F K s G L) (f:BlankM (RX F P) (BX K P) i)(hp:i ∉ S)(Hv:ψS σ S)(q':S.length≤2)(U₀:poke_F σ p.val.2 S.toFinset) : let P':= P+(FrameT (RX F P) (BX K P)).insertΦ p σ S x i; let H:=sayQ C U (ΓNow σ F P') (ΦNow σ K P'); let Z:= sayQ C U (ΓNow σ F P) (ΦNow σ K P); (∀ l:List I,ψS σ l→ i∉l → tipI H l= tipI Z l) ∧ ∀ l: List I, ψS σ (i::l) →(∀ j∈ S,j∉l) → tipI H (i::l)=(x:ℂ) • tipI Z (S++l):=by
 intro P' H Z
 let A:=(FrameT (RX F P) (BX K P)).insertΦ p σ S x i
 have uG:=ReefX.registry_plus σ cloudP (T:=PitR C h 1) ReefxR t.white t.active
 have H1:=ReefX.registry_plus σ cloudP (T:=PitR C h 1) ReefxR fV uG
 have H2:= ReefX.registry_plus σ cloudK (T:=PitF C h 1 k) (ReefxF k) tV t.bank
 have V':= frameL σ (RX F P) (BX K P) C h 1 k _ _ H1 H2
 have hL(z):= Γ_formula σ (RX F P) (BX K P) C h 1 _ H1 U d z; have hK(z):= Φ_formula σ (RX F P) (BX K P) C h 1 k _ H2 z U
 let X:= (K0).addCosto p σ S x i (ΓNow σ F P); let Y:= (K0).BankoB p σ S x i (ΦNow σ K P)
 have hP(z y):ΓNow σ F P' z y=X z y:=by change Canz σ _ (RX F (P+A)) _ _=_; rw[show RX F (P+A)=RX F P+pureX A from (by change F+(P.X+A.X + (P.Y+A.Y))= F+(P.X+P.Y)+ (A.X+A.Y); abel), puff_add]; rfl
 have hY(z y):ΦNow σ K P' z y=Y z y:=by change Canz σ _ (K+(P.B+A.B)) _ _=_; rw[←add_assoc,puff_add]; rfl
 change (∀ l: List I,ψS σ l→ i∉l → tipI (sayQ C U (ΓNow σ F P') (ΦNow σ K P')) l= _) ∧ ∀ l: List I, ψS σ (i::l)→(∀ j∈ S,j∉l)→ tipI (sayQ C U (ΓNow σ F P') (ΦNow σ K P')) (i::l)=_
 rw [show ΓNow σ F P'=X from funext fun i=>funext (hP i), show ΦNow σ K P'=Y from funext fun i=>funext (hY i)]
 refine ⟨fun l hp p0=> unchanged4 (K0) p σ C U S x i (ΓNow σ F P) (ΦNow σ K P) d hL hK l p0 hp,fun l g t=>?_⟩
 apply height_p (K0) p σ C U S ⟨fun i g=>(V'.refs i g).2,fun i g=>(V'.rolls i g).2⟩ U₀ x i _ _ d hL hK (List.Nodup.of_map σ Hv) q' hp _ g t
 funext v; change exp (exponentL _ (ΓNow σ F P (dune i v)) _)*fueled _ (ΦNow σ K P (dune i v)) _=_; rw[show ΓNow σ F P (dune i v)=ΓNow σ F P v from funext (fun j=>blank_C σ i _ f.1 _ v), show ΦNow σ K P (dune i v)=ΦNow σ K P v from funext (fun j=>blank_C σ i _ f.2 _ v)]; rfl
end
-- ledger definition induct.Serp. needs output group disjoint.APort.All ***unpermuted*** S or S.Perm. include Gen.Any nonoccurrence. UVis.
inductive Vote : List I → List I → List I → ℂ → Prop where
 | stays (l:List I) (h:ψS σ l): Vote [] l l 1
 | withoutK (i:I) (L output t:List I)(c:ℂ) : Vote L output t c → i∉ output → ψS σ output → Vote (L++[i]) output t c
 | expand (i:I)(L output l t:List I)(c:ℂ): Vote L (s i ++ l) t c→ (∀ k∈ s i,k ∉ l) → output.Perm (i::l) → ψS σ (i::l) → Vote (L++[i]) output t ((μ i:ℂ)*c)
include fV tV v q d
-- any slices along transcript.Done.
lemma PledgeV (V Φ:ℝ)(L M:List I)(l t:List I)(p:ℂ)(g:Vote σ μ s L l t p)(w:Rider4 ℓ Ω η a b (rental b a η T Y) ((L++M).map σ) V Φ)(pΦ: FlushL σ μ G ℓ a b L)(p0:Things σ F K s G L): tipI (quakeY σ F K μ s G C L U) l=p • tipI (quakeY σ F K μ s G C [] U) t:=by
 have Grow {L:List I}{j:I}(p':Things σ F K s G (L++[j]))(f':FlushL σ μ G ℓ a b (L++[j])) : Things σ F K s G L ∧ FlushL σ μ G ℓ a b L∧ j∉L :=by
    exact ⟨⟨fun i p=>p'.face i (by simp[p]),fun i p=>p'.proc i (by simp[p]), by simpa using List.Nodup.of_append_left p'.noble,fun i p=>p'.womb i (by simp[p])⟩,⟨fun i p=> f'.frame i (by simp[p]),fun i p=> f'.costB i (by simp[p]),fun i p=> f'.p0 i (by simp[p])⟩, fun v=> (List.nodup_append.mp p'.noble).2.2 j v j (by simp) rfl
      ⟩
 have hh(L:List I)(j:I)(M)(p:Things σ F K s G (L++[j]))(f:FlushL σ μ G ℓ a b (L++[j]))(t:Rider4 ℓ Ω η a b (ηL) ((L++[j]++M).map σ) V Φ): let H:=quakeY σ F K μ s G C (L++[j]) U; let X:=quakeY σ F K μ s G C L U; (∀ l:List I,ψS σ l→ j∉l → tipI H l= tipI X l) ∧ ∀ l: List I, ψS σ (j::l) →(∀ i∈ s j,i∉l) → tipI H (j::l)=(μ j:ℂ) • tipI X (s j++l):=by
    intro H X; obtain ⟨u,v',w⟩:=Grow p f; let Pi:= ProgramL σ F K μ s G L
    rw [List.append_assoc] at t; obtain ⟨W,H₁,Wt⟩:= Skalp σ F K T Y μ s G C h _ _ _ _ b k fV tV v q V Φ L (j::M) t v'; have hw:j∈L++[j]:=by simp
    have k':= BankIt σ F K μ s G L j w (p.face _ hw)
    have e := Lprep σ F K T Y s G C h _ fV tV U d j (G j) (s j) (μ j) L Pi W H₁ (f.frame _ hw) u k' (p.proc _ hw) (p.womb _ hw).2.1 (p.womb _ hw).1 (p.womb _ hw).2.2
    have tH:H= sayQ C U (ΓNow σ F (turnY σ F K μ s G Pi j)) (ΦNow σ K (turnY σ F K μ s G Pi j)):=by unfold H quakeY ProgramL; rw [List.foldl_append]; rfl
    rw [tH]; exact e
 induction g generalizing M with
 | stays l u=>rw [one_smul]
 | withoutK j L l t e p g h ih=>
    obtain ⟨m,hz,h'⟩:= Grow p0 pΦ; rw [(hh L j _ p0 pΦ w).1 _ h g]; apply ih (j::M) _ hz m; rw [List.append_assoc] at w; exact w
 | expand j L l t f' c e p g h ih=>
    have hx:= move_ζ g (say_r σ F K C U d (ProgramL σ F K μ s G (L++[j]))) roots; rw [show tipI _ l= _ from (show tipI (Gm (L++[j]) U) l=_ from hx)]; change tipI (Gm (L++[j]) U) (j::t)= _; rw [show tipI (Gm (L++[j]) U) (j::t)=_ from (hh L j _ p0 pΦ w).2 _ h p]; obtain ⟨e,h0,h1⟩:=Grow p0 pΦ; rw[ih (j::M) _ h0 e,mul_smul]; rw[List.append_assoc] at w; exact w
#print axioms PledgeV
end
end
end Iona
end YM.CF.Scree.Ing
end
