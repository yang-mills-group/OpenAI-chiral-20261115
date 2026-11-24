import YM.CF.Tale.Limb
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Projection
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Tale
set_option quotPrecheck false
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
-- Transverse linear gauge moment, transported spot. canonical blocks only. no t-period interpolation
variable (k:ℝ)(j t:ℕ)(h:0<k)(p:4≤j)(v:4≤t)(P:Flight j t)
variable {f c:Side}(w:f.val=c.val *P.L.val)(o:Site f)(d b a:Axis)(i:TypeFace 1)
open MultiNext.SignedSource
local notation "Z"=> Exterior.coord d
local notation "L"=> P.L
local notation "G"=> deckY j t P w
local notation "R"=> Lt k j t P
local notation "T"=> advanceC L R [a]
local notation "y"=> (deckY j t P w).residue o
local notation "U"=> T (y,i) Z
open Next.SectorChange Pressure Tube
open MultiNext.SignedSource.Newt
local notation "D2"=>SU.group.Color
local notation "B_"=> Body 1 c
local notation "U'"=> ((G).parent o)
open AnalyticBridge.VerifiedReset
variable {n: Side}
abbrev townX(r:Side):= Directions SU.group r
def curt (r:ℕ)(o:Site c): townX c →L[ℝ] townX c:= ContinuousLinearMap.pi fun i=> if separation o i.1 ≤ r then ContinuousLinearMap.proj (φ:=fun _=>D2) i else 0
lemma curtP(r:ℕ)(x:Site c)(i:townX c)(j:Bond c): curt r x i j= if separation x j.1 ≤ r then i j else 0:=by
 unfold curt; simp only [ContinuousLinearMap.pi_apply]; split <;> rfl
lemma near_q(c f:Side)(r:ℕ)(Rq:Ratio c f)(o:Site c)(x:Site f)(p: separation x (Rq.embed o) ≤ r)(h:2*r < Rq.count.val): Rq.parent x=o:=by
 let j:=Rq.parent x; have ht := Laic.emptio Rq j o; have he:= separation_triangle (Rq.embed j) x (Rq.embed o); rw [ht,separation_comm _ x] at he; have he':= Corona.near Rq x
 by_contra hg; have hv:1 ≤ separation j o:=by
    by_contra e; apply hg; have hp: Lattice.lift (j-o)=0:=by ext x; have ht:(Lattice.lift (j-o) x).natAbs≤ separation j o:=component_le ..; rw [Pi.zero_apply]; omega
    exact sub_eq_zero.mp ((wrap_lift _).symm.trans ((congrArg _ hp).trans (map_zero _)))
 have hq:Rq.count.val≤ Rq.count.val*separation j o:=Nat.le_mul_of_pos_right _ hv; change 2*separation x (Rq.embed j) ≤ _ at he'; omega
-- prepared. anchor o; test primitive wedge clipped horizon
variable (x:Site c)(r m:ℕ)(Z_:PlaqAxes)(X:SU.group.Color)
local notation "D'"=> (curt r x ( (AnalyticBridge.VerifiedReset.wedge Z_ X).field x))
private lemma ears_D (y':Site c)(b:Axis): D' (y',b)=if separation x y' ≤ r ∧ Z_.val.2=b then (AnalyticBridge.VerifiedReset.coord x y' Z_.val.1) • X else 0:=by
 rw [curtP, AnalyticBridge.VerifiedReset.wedge_field]; split_ifs<;> grind
include w
omit w in
private lemma m_arch (b':TypeFace 1):b'=Exterior.coord Z_.val.2 ↔ Exterior.axisEquiv.symm b'= Z_.val.2:=by
 rw [← Equiv.eq_symm_apply]; rfl -- tune arg
private lemma delta_p (h:x=(G).parent o)(hx:m ≤ r)(hQ:2*m<c.val)(v':Cover)(hp: Laurent.size v' ≤ m)(b':TypeFace 1) :Next.SectorChange.Flat.labels D' (stem c v' U',b')=nickV X v' Z_.val.2 Z_.val.1 b':=by
 unfold nickV; rw [← h]; change D' (_,Exterior.axisEquiv.symm b') = _; rw [ears_D]
 have he: separation x (stem c v' x) ≤ m:=by unfold stem; rw [separation_comm,separation,add_sub_cancel_left]; exact (wrapped ..).trans hp -- amb
 have hh:AnalyticBridge.VerifiedReset.coord x (stem c v' x) Z_.val.1=v' Z_.val.1:=by
    unfold AnalyticBridge.VerifiedReset.coord stem; rw [add_sub_cancel_left]; apply congrArg (fun t:Cover=> (t Z_.val.1:ℝ)); refine Lattice.lift_eq_iff.mpr ⟨rfl,fun i=>?_ ⟩; have hv:(v' i).natAbs≤ m:=(single_le_sum (f:=fun j:Axis=> (v' j).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i)).trans hp; omega
 simp only [he.trans hx,true_and]; simp_rw [hh, eq_comm (a:=Z_.val.2),m_arch] -- tune
private lemma duct_D (a₀ C:ℝ)(q:0 ≤ C)(u:∀ i:ℕ,(1+(i:ℝ))≤ Real.exp (a₀/2*i)*C)(v':Cover)(b':TypeFace 1)(h:x=(G).parent o): ‖Next.SectorChange.Flat.labels D' (stem c v' U',b')-nickV X v' Z_.val.2 Z_.val.1 b'‖ ≤ 2*C*‖X‖*Real.exp (a₀/2* Laurent.size v'):=by
 rw [←h]; let Y:= stem c v' x; let D:= Exterior.axisEquiv.symm b'; change ‖D' (Y,D) - _‖≤ _; let W':ℝ:= Laurent.size v'; have hz:0 ≤ W':=Nat.cast_nonneg _; have hp': ‖D' (Y,D)‖≤ W'*‖X‖:=by
    rw [ears_D]; split; swap; rw [norm_zero]; positivity
    rw [norm_smul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); have hY: separation Y x ≤ Laurent.size v':=by unfold Y stem; rw [separation,add_sub_cancel_left]; exact wrapped ..
    exact (small_coord ..).trans (Nat.cast_le.mpr hY)
 refine (norm_sub_le ..).trans ((add_le_add hp' (d:=W'*‖X‖) ?_).trans ?_) -- incorrect b arg
 · change ‖nickV _ _ _ _ _‖ ≤ W' *‖X‖; unfold nickV; split; swap; rw [norm_zero]; positivity
   rw [norm_smul]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); simpa using (Push.Loops.axis_le_size v' Z_.val.1)
 have h:=u (Laurent.size v'); calc
    _ = W'*(2* ‖X‖):=by ring
    _ ≤ _:= (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left zero_le_one).trans h) (by positivity:0 ≤2*‖X‖)).trans_eq (by ring)
-- quote.Rio
omit w
include h p v
lemma joint_T:∃ a₀ C:ℝ,0<a₀∧ 0<C∧∀ (P:Flight j t),∀ c f:Side,∀ (w:f.val=c.val *P.L.val)(o:Site c)(Px:Site f), (deckY j t P w).parent Px=o→∀ (X:group.Color)(Q:PlaqAxes)(r m:ℕ), m ≤ r→ 2*m<c.val→∀ a:Axis,∀ i:TypeFace 1, let Dx₁:= Next.SectorChange.Flat.labels (curt r o ((AnalyticBridge.VerifiedReset.wedge Q X).field o)); let V':=MultiNext.SignedSource.Newt.load (installed (deckY j t P w) (Lt k j t P)) Dx₁; ‖V' (Px+step a,i)- V' (Px,i)- (modeT P.L a Q.val.1 i (Exterior.coord Q.val.2)) • X‖≤ (C/(P.L.val:ℝ)^2)*(‖X‖*Real.exp (-a₀*m)) :=by
 obtain ⟨a₀,C,hA,hC,H⟩:= (secure_both k h p v).1.honored p 1; obtain ⟨Zs,g,hs⟩:= length_mom 1 (half_pos hA);
 refine ⟨a₀/2,Fintype.card (TypeFace 1)*(2*Zs*C),by positivity,by have he : Nonempty (TypeFace 1):=⟨Exterior.coord 1⟩; positivity,fun P c f w o O ho X J r m hp0 hN a i=>?_⟩
 intro Dv V' -- notation conflict
 let U_:=AnalyticBridge.VerifiedReset.wedge J X; let K:=curt r o (U_.field o); change ‖MultiNext.SignedSource.Newt.load _ _ _-MultiNext.SignedSource.Newt.load _ _ _- _‖≤ _; rw [ζuse k j t h p v P w] -- tune arguments
 have he: Row.strip (advanceC P.L (Lt k j t P) [a]) a₀ (C/(P.L.val:ℝ)^(1+[a].length)):= H P _ (by simp; omega)
 refine (pipe_u k j t h p v P w O _ _ a i _ X ((show J.val.1<J.val.2 from J.property).ne) he hA (2*Zs*‖X‖) (by positivity) (fun i h B=>delta_p j t P w O o r m J X ho.symm hp0 hN _ h B) (fun B x=>duct_D j t P w O o r J X a₀ Zs g.le (fun i=>by simpa only [pow_one] using hs i) B x ho.symm)).trans_eq ?_; change (Fintype.card _ :ℝ)* ( _ * _*(C/(P.L.val:ℝ)^2))=_; ring
end YM.CF.Tale
