import Anomaly.Market.Tariff
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Regis.Head.GeometryP
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam Matrix ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {c n : Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ ε Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f l m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)
open CF.Swell.Sonar Garland Etch Next.Free Push.Local
variable {I J:Type*} [Fintype I][Fintype J] {T D:ℝ}
lemma maskSafe (s:Signed)(b o:Site n) (T:withinCore r A (face_anchors (misdemean p.threshold U)) (hallBill m) (affine s b o))(q:l+2≤hallBill m) : Healthy p.threshold (halo l {o}) (pull s b U):=by
 apply (healthy_pull s b ..).mp; rw [halo_plan]; apply disjoint_left.mpr; intro i h t; obtain ⟨x,L,k⟩:=(flags_spec ..).1 t; apply T.2 (halo_spec.mpr ⟨x.1,mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,k⟩),?_⟩); have ht:= (doors (b:=l) i).1 h
 apply (separation_triangle x.1 i (affine s b o)).trans; have hx:=Work.E01.sep_touched x i L; rw [separation_comm i (affine s b o)]; omega -- tune
lemma zoneWords {D:Dir G n}(T:withinCore r A (face_anchors (misdemean p.threshold U)) (hallBill m) o)(f:TrustLogs D U r A v)(hv:v≤R.c)(q:l+1≤hallBill m): Agrees (halo l {o}) U (represent D):=by
 intro e p x; have ht:= (doors (b:=l) e.1).1 p; have hx: Safe r A 1 e.1:=(T.shift (d:=show separation o e.1+1≤_ from by omega)).1
 -- Working require Safe ensures
 obtain ⟨u,h⟩:= f e ⟨hx.1,safeIn hx le_rfl⟩; unfold represent increment; rw [u, Pi.one_apply, mul_one,R.records _ (h.trans hv)]
lemma forest_yaw (s:Signed)(b o:Site n){D:Dir G n} (T:withinCore r A (face_anchors (misdemean p.threshold U)) (hallBill m) (affine s b o))(f:TrustLogs D U r A v)(hv:v≤R.c)(q:l+1≤hallBill m): Agrees (halo l {o}) (pull s b U) (represent (bank s b D)):=by
 have hp:= bank_at s b D 1; rw [one_smul,one_smul] at hp; rw [hp]; refine ProjectorNext.Equivariance.agrees_pull _ _ _ ?_
 let T':= (turnSites s b); rw [show image (affine s b) (halo l {o}) = halo l {affine s b o} from (halo_plan ..)]; exact zoneWords T f hv q

-- Portal lookup coefficients. bind scalar λ in √ inverse sqrtβ/v normalization.
lemma smallShelf {κa:Dir G n} (j: Face (Per n)) (T:withinCore r A (face_anchors (misdemean p.threshold U)) (Sequest m) j.1)(ht:4≤Sequest m)(u:TrustLogs κa U r A v) (h:0≤v)(v0:v≤R.c):‖faceCurl j κa‖≤p.threshold+faceCutError R v:=by -- tune declare κa
 obtain ⟨f,v'⟩:=angleFaceSmall u h v0 j (T.1.shift (y:=j.1) (by simp; exact ht)); have hp:G.chord (faceValue U j)≤p.threshold:=by
    by_contra! h; exact T.2 (halo_subset _ _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,h⟩))) -- tune
 refine le_trans (norm_le_norm_sub_add _ (G.curvature (faceValue U j))) ?_; rw [norm_sub_rev]; exact (add_le_add v' ((G.curvature_norm _).trans hp)).trans_eq (add_comm ..)

lemma collect_boundS (s:Signed)(b:Site n)(v:Dir G n)(h:ProbeBox v w)(t:0≤w): ‖collect G (bank s b v)‖ ≤ w:=by
 refine (pi_norm_le_iff_of_nonneg t).2 (fun i=>?_); unfold bank; change ‖Bid.pulled _ s _‖≤ _; unfold Bid.pulled; dsimp only
 let j:= (posDir (axisEquiv.symm (coord i.2))).rotate s
 let e:= j.used (affine s 0 i.1); have hu:‖arbor b v (e.1,coord e.2)‖ ≤ w:= h (e.1+b,e.2)
 split
 · rw [norm_neg]; exact hu
 exact hu

lemma featherS (s:Signed)(j:Face (Per n))(b:Site n) : separation (affine s b j.1) (Face.send s b j).1≤2:=by
 have ht: affine s b j.1∈touched (Face.send s b j):=by rw [Work.H03.touched_send]; exact mem_image_of_mem _ (Work.E01.base_touched _)
 rw [separation_comm]; exact Work.E01.sep_touched _ _ ht
-- input coefficient.Local-on-S supports all origins.
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](P_:tableQ G n E)
-- local notation "ω"=> face_anchors (misdemean p.threshold U)
local notation "Z'"=>  hallBill m
lemma lump (s:Signed)(b':Site n)(ρ:ℝ)(Q Y:Dir G n) (t:withinCore r A (face_anchors (misdemean p.threshold U)) (hallBill m) (affine s b' o))(e:l + 2+ Sequest m ≤ hallBill m)(pB:0<β)(d:TrustLogs (Q+Y) U r A v)(f:v ≤ R.c)(h:0≤v)(hW:Regional o l P_)(uH:0<D)(fX: |ρ| * (p.threshold+faceCutError R v)≤D):
 let x:= starFeed B P r A (face_anchors (misdemean p.threshold U)) m Y β Q
 coverT P_ s b' q (ρ*coupling β) D x= ρ^2 • tariff P_ (receipt (bank s b' (Q+Y))):=by -- ρ polynomial homog
 intro x; unfold coverT tariff; rw [smul_sum]; apply sum_congr rfl; intro i _; by_cases y:P_ i=0; · rw [y,smul_zero,smul_zero,smul_zero]
 have hx(j:Fin 2):
    let b:= (i j).1
    withinMark r A (face_anchors (misdemean p.threshold U)) m (Face.send s b' b):=by
    intro b; refine t.shift (z:=(Face.send s b' b).1) ?_
    have h1:=featherS s b b'; have h2:= (doors _).1 (hW i y j); have hV: separation (affine s b' o) (affine s b' b.1) ≤ l := by simp only [affine,separation_translate,separation_signed]; exact h2 -- specify

    apply le_trans (Nat.add_le_add_right (separation_triangle _ (affine s b' b.1) _) _); omega
 have hl(j:Fin 2) : snub D (giveAt s b' q (ρ*coupling β) x (i j))= ρ*receipt (bank s b' (Q+Y)) (i j):=by
    let b:= (i j).1; let J:=Face.send s b' b; have he: river q J x=(coupling β)⁻¹ • faceCurl J (Q+Y):=by unfold x starFeed; rw [map_smul, river_still B P J (hx j)]
    let u:=turned s b.2; have ht:|u|=1:=by unfold u; nlinarith [sq_abs (turned s b.2), turned_sq s b.2, abs_nonneg (turned s b.2)]
    let x':=faceCurl J (Q+Y); let y':= x' (i j).2
    have hk: giveAt s b' q (ρ*coupling β) x (i j)= ρ * (u*y'):=by change u*_ *((river _ J x) (i j).2)=_; rw [he]; change u*(ρ*coupling β)*((coupling β)⁻¹ * y')=_; have hq:=coupling_pos pB; field_simp
    have hi: |ρ* (u*y')|≤D:=by rw [abs_mul,abs_mul,ht,one_mul]; apply le_trans _ fX; refine mul_le_mul_of_nonneg_left ((show |y'|≤‖x'‖ from norm_pin ..).trans (smallShelf J (hx j) (by unfold Sequest; omega) d h f)) (abs_nonneg _)
    rw [hk,(snub_budget uH _).2.2 hi]; unfold receipt; rw [heading]; rfl
 simp_rw [hl]; rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,mul_smul]
where norm_pin(x:G.Color)(i:G.ColorIndex):|x i|≤‖x‖:=by rw [←EuclideanSpace.basisFun_inner]; simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) x
end YM.Regis.Head.GeometryP
