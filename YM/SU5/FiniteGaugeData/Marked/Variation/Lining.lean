import YM.SU5.FiniteGaugeData.Marked.Variation.Scissors

/-! # Menu interpretation of fixed chiral words under Advance -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Fock Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange
open Reed (Fine)
attribute [local instance] opCStarAlgebra
section
variable {X I:Type*}[MeasurableSpace X]{V:I→Type*}[∀i,NormedAddCommGroup (V i)][∀i,NormedSpace ℝ (V i)]
variable {J : I→ Type*}[∀i,Fintype (J i)]
lemma circle {f:∀i,J i→ X→V i}(h:Menu (T:=fun i:Σ t,J t=> V i.1) (fun i:Σ t,J t=> f i.1 i.2)):
 Menu (T:=fun i:I=>V i) (fun i x=> ((Fintype.card (J i):ℝ)⁻¹) • ∑ t, f i t x):=by
 have hx (i:I)(a:J i → V i)(ε:ℝ)(p:0≤ε)(t:∀j,‖a j‖≤ ε): ‖((Fintype.card (J i):ℝ)⁻¹) • ∑ j,a j‖ ≤ ε:=by
    obtain n|e:= isEmpty_or_nonempty (J i)
    · simpa using p
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=>t i))) (by positivity)).trans_eq ?_
    rw [Finset.sum_const,card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ (by positivity), one_mul]
 obtain ⟨C,c,u⟩:=h.budget
 refine ⟨?_, C,c,fun i x=> hx i _ _ c (fun j=> u ⟨i,j⟩ x)⟩
 intro ε e; obtain ⟨P,v,p⟩:=h.deal _ (half_pos e); refine ⟨P,v,fun x y s i=>?_⟩
 rw [dist_eq_norm,←smul_sub,←sum_sub_distrib]; refine lt_of_le_of_lt (hx i _ (ε/2) (by linarith) ?_) (by linarith)
 exact fun j=> (show dist (f i j x) (f i j y)< _ from p x y s ⟨i,j⟩).le.trans_eq' (by rw [dist_eq_norm])
end
private lemma velvet_op {X I:Type*}[MeasurableSpace X]{N:I→Side}{f:(i:I)→ X→ Ket (Single (N i))}(h:Menu f): Menu (T:=fun i=>FC (Single (N i))) (fun i x=>create (f i x)) ∧ Menu (T:=fun i=>FC (Single (N i))) (fun i x=>Fock.remove (f i x)):=by
 obtain ⟨C,v,t⟩:= h.budget
 have he(k:Side)(i:Ket (Single k)):‖create i‖ ≤ ‖i‖:=Flare.cost_pe false _
 have a:Menu (T:=fun i=> FC (Single (N i))) (fun i x=>create (f i x)):=by
    refine ⟨Deal.along (fun i (x:Ket (Single (N i)))=>create x) h.deal ?_,C,v,fun i x=>(he _ _).trans (t i x)⟩
    intro ε p; refine ⟨ε,p,fun i x y h=>?_⟩; rw [dist_eq_norm,←map_sub]; exact lt_of_le_of_lt (he ..) (by simpa only [dist_eq_norm] using h)
 refine ⟨a, ⟨Deal.along (fun i (x:FC (Single (N i)))=>star x) a.deal ?_,C,v,fun i x=>?_⟩⟩
 · intro ε p; refine ⟨ε,p,fun i x y h=>?_⟩; rw [dist_eq_norm,←star_sub,norm_star]; simpa only [dist_eq_norm] using h
 dsimp only [Fock.remove]; rw [norm_star]; exact (he _ _).trans (t i x)

variable {X I : Type*} [MeasurableSpace X](N:I→ Side)(L:Side)(P:I→Side)(sz:∀i,(P i).val=(N i).val*L.val)
local notation "G" => bead N L P sz
variable (j D:ℕ)(vA:LaurentRadius j L D)(ho: Odd L.val)
variable (M:I→ Male)(Q: I→Op SU.Slot){d:ℝ}(y:∀i,‖Q i‖ ≤ d)
variable (w:(i:I)→ X→ Nom (N i) (P i))(pay:∀ a:(i:I)→ Edge (Site (More (P i))),Deal (I:=I) (fun i x=> (w i x).1 (a i):I→X→SU.E))

/-- the cover-language insertion spelled without size calibration. -/
def thread (n:Side)(a:Blot): FC (Single n):= if a.2.1 ∈ plusHalf then create (basisC n a.1 a.2.1 a.2.2) else Fock.remove (basisC n a.1 a.2.1 a.2.2)
def spool (n:Side)(u:Chorus): FC (Single n):=(u.map (thread n)).prod
abbrev wholeZ (n:Side)(u:Chorus) : Buffered.Mark n:= fun _=> spool n u

def knot (n:Side)(u:Chorus)(f:PairsC→ℂ): Buffered.Mark n:= fun v=> f (Prod.map (onC n) (onC n) v) • spool n u
lemma spool_cons {n:Side}(x:Blot)(y:Chorus):spool n (x::y)=thread n x*spool n y:=rfl
lemma spool_sing (K:Calibration)(m:Side)(u:Chorus)(v:Fields (K.c m)):sing K u m v=spool (K.c m) u:=by
 induction u with
 | nil=> rfl
 | cons x y ih=> rw [spool_cons]; change Sound.chord K x m v * sing K y m v=_; rw [ih]; unfold Sound.chord thread; split <;> rfl
lemma kiosk (K:Calibration)(m:Side)(u:Chorus)(f:PairsC→ℂ):note K f u m=knot (K.c m) u f:=funext fun x=> by rw [note_v,spool_sing]; rfl
private theorem bUp {i n}(x b)(p:i∈plusHalf): withinM (Tset n) (basisC n x i b):=by unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index n x i b) ((mem_Tset ..).mpr p)]
private theorem bDown {i n}(x b)(p:i∉plusHalf): withinM (Tset n)ᶜ (basisC n x i b):=by unfold withinM basisC; rw [map_smul,within_basis (Tset n)ᶜ (Lifted.index n x i b) (mem_compl.mpr fun h=> p ((mem_Tset ..).mp h))]
private lemma thread_fine (n:Side)(x:Blot):Fine (Tset n) univ true (thread n x):=by
 unfold thread; split
 next h=>exact fine_create _ (bUp _ _ h) (within_univ _)
 next h=>exact fine_remove _ (bDown _ _ h) (within_univ _)
lemma spool_fine (n:Side)(u:Chorus):Fine (Tset n) univ (treble u) (spool n u):=by
 induction u with
 | nil=> exact Fine.one
 | cons x y ih=> exact Fine.grow (thread_fine ..) ih
--
include D vA y pay ho
private lemma wind_spool (x:Blot):Menu (T:=fun i=>FC (Single (P i))) (fun i a=>subF (G i) j (Q i) (M i) ho (w i a) (thread (N i) x)):=by
 unfold thread
 let m(i:I):= basisC (N i) x.1 x.2.1 x.2.2
 have econ (b:Bool): Menu (T:=fun i=>Ket (Single (P i))) (fun i a=>byMode (G i) j (Q i) (M i) (w i a) b (m i)):=by
    unfold m basisC; simp_rw [map_smul]; exact (Menu.cnst (fun i :I=> winding (N i) x.1) zero_le_one (fun _=> (Rush.fee_norm _).le)).scale (gifted N L P sz j D vA w pay M Q y b _)
 split
 · next h=> simp_rw [sub_create (G _) j _ _ ho _ (bUp _ _ h)]; exact (velvet_op (econ true)).1
 next h=> simp_rw [sub_remove (G _) j _ _ ho _ (bDown _ _ h)]; exact (velvet_op (econ false)).2
lemma wool (u:Chorus):Menu (T:=fun i=>FC (Single (P i))) (fun i a=> subF (G i) j (Q i) (M i) ho (w i a) (spool (N i) u)):=by
 induction u with
 | nil=> simp_rw [spool,List.map_nil,List.prod_nil,sub_one]; exact Menu.cnst _ zero_le_one (fun i=>norm_one.le)
 | cons x u ih=> simp_rw [spool_cons,sub_mul (G _) j _ _ ho _ (thread_fine ..) (spool_fine ..)]; exact (wind_spool N L P sz j D vA ho M Q y w pay x).mul ih
omit pay
-- W fixed arbitrarily with respect to X
variable (w':(i:I)→ Fields (P i))(t:(i:I)→X→Fields (N i))(z:Deal (I:=Σ i:I,Edge (Seat (N i))) (T:=fun _=>SU.E) (fun a x=> (t a.1 x).2 a.2))(q:Chi)(e:ℝ)
variable (hx:0<e)(hg:2*e<firstRadius SU.group)
include z hx hg
omit D vA y ho
omit z in
private lemma keel:Continuous (fun x:SU.E × SU.E=> knit q e x.1 x.2):= (SU.group.lieExp_cont.comp ((patched_continuous q hx hg).comp (continuous_fst.mul continuous_snd.inv))).mul continuous_snd
private lemma screen (H:(i:I)→Forest (ratio (G i)))(a:(i:I)→Edge (Seat (P i))): Deal (I:=I) (fun i x=>seine (G i) (H i) q e (w' i).2 (t i x).2 (a i)):=by
 let u:(i:I)→ Seat (P i)→SU.E:=fun i v=> ((H i).foldAt (w' i).2 v)⁻¹
 let B:=fun i=> gauge (H i|>.foldAt (w' i).2) (w' i).2 (a i)
 have h:Deal (f:=fun (i:I)(x:X)=> Precision.replica (ratio (G i)) (show Config SU.group _ from (t i x).2) (a i)):=by
    unfold Precision.replica
    let k(i:I):Seat (N i):=(ratio (G i)).parent (a i).1; let v(i:I):Axis:=(a i).2
    let Y(i:I):Prop:= (ratio (G i)).parent ((a i).1+Lattice.step (v i)) = k i
    have ht:= z.re fun i:I=>(show (Σ i,Edge (Seat (N i))) from ⟨i,k i,v i⟩)
    refine (Deal.cond (T:=fun _=>SU.E) (Deal.pure (fun _:I=> (1:SU.E))) ht Y).congr ?_
    intro i x; by_cases h:Y i
    · dsimp only; rw [if_pos h,if_pos h]
    dsimp only; rw [if_neg h,if_neg h]
 have hK:Deal (fun (i:I)(x:X)=>portU (G i) (H i) q e (w' i).2 (t i x).2 (a i)):= ((Deal.pure (X:=X) (T:=fun _=>SU.E) B).prod h).post (keel q e hx hg) -- remove unused
 let u':I→SU.E:= fun i=> u i (a i).1
 let m:I→SU.E:=fun i=> (u i ((a i).1+Lattice.step (a i).2))⁻¹
 exact (((Deal.pure (X:=X) (T:=fun _=>SU.E) u').prod hK).post (continuous_fst.mul continuous_snd) |>.prod (Deal.pure (X:=X) (T:=fun _=>SU.E) m)).post (continuous_fst.mul continuous_snd)
include D vA y ho
theorem stitched (U:Chorus): Menu (T:=fun i=>FC (Single (P i))) (fun i x=> gathered (G i) j (Q i) (M i) ho q e (wholeZ (N i) U) (w' i) (t i x)):=by
 -- all forests per period before averaging
 let J(i:I):=Forest (ratio (G i)); let n(a: Σ i,J i):=N a.1; let r(a:Σ i,J i):=P a.1
 refine circle (J:=J) ?_
 refine wool n L r (fun a=> sz a.1) j D vA ho (fun x=> M x.1) (fun a=> Q a.1) (fun a=> y a.1)
    (fun x u=> middle (G x.1) q e x.2 (w' x.1) (t x.1 u)) ?_ U
 intro a
 exact screen n L r (fun a=> sz a.1) (fun a=>w' a.1) (fun a x=>t a.1 x)
    (z.re fun a:(Σ i:(Σ i,J i), Edge (Seat (n i)))=>⟨a.1.1,a.2⟩) q e hx hg (fun f=> f.2) a
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.stitched
