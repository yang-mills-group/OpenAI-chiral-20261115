import SatinThinScar
import YM.SU5.Gleam.Inlets
/-! # Combine warp & portfolio. From Elevation, Shelter -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology ENNReal Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}
variable (B:Z.Bounds q η C S)

abbrev twice_rich (Z:PathData G)(q:Clip)(p:BudgetPoint) (β κ ξ ε:ℝ)(U:Config G n):= Real.exp (-(Z.principal q p β U)+κ*(misdemean p.threshold U).card+ ξ*(misdemean ε U).card)
variable {u y ε:ℝ}{Λ:Finset (Cell n)}
include B
lemma income_burs : Envelope (twice_rich Z q p β κ ξ ε (n:=n)):= (((PathData.principal_env B p β).neg.add (conduct ..)).add (conduct ..)).exp
lemma twice_gauge : GaugeInvariant (twice_rich Z q p β κ ξ ε (n:=n)):= by
 have he(U:Config G n): twice_rich Z q p β κ ξ ε U= richG Z q p β κ U*Real.exp (ξ*(misdemean ε U).card):=Real.exp_add ..
 intro k U; rw [he,he,richG_inv B k,malaise_home]
lemma at_shelf (t:ε≥p.threshold)(d:A=broken r ε U)(dd:Λ=misdemean p.threshold U)(l:EnoughMark q p m)(d':0≤β)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v)(p':blank X r A (face_anchors Λ) m)(s:0 ≤ v)(t':v≤ R.c)(hv:0 ≤ C)(hx:0 ≤ y)(hz:κ+u ≤ β*unitDueS q p)(hx':ξ+21^4*y ≤ β*unitDueL q p ε) : twice_rich Z q p β κ ξ ε U ≤ Real.exp ((-β*∑ b:Cell n,arrear Z q r A (face_anchors Λ) m b X Y) + (taxΔ R q n p β v η C S m - u*Λ.card - y*A.card)):=by
 let T:= CF.Graph.taxY n β p.threshold C S; let F(b:Cell n):= arrear Z q r A (face_anchors Λ) m b X Y; let Y'(b:Cell n):= Z.baseTerm q p U b; let ts:=unitDueS q p; let tv:=unitDueL q p ε; let m':ℝ:=Λ.card; let mL:ℝ:=(misdemean ε U).card; let R':=(21:ℝ)^4
 apply Real.exp_monotone
 have hr:(∑ b:Cell n,F b)+ (ts*m'+tv*mL)≤ (∑ b:Cell n,Y' b)+(Fintype.card (Cell n):ℝ)*Δ₁ R q v m η C:=by
    unfold m' mL F ts tv Y'; subst A Λ; have he:= sum_le_sum (s:=univ) fun i _=> scar_line (b:=i) B t f g h p' l s t' hv; simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,counts_tax] at he; simpa only [Δ₁,mul_add] using he
 have hC:= mul_le_mul_of_nonneg_left (show (A.card:ℝ)≤ mL*R' from (by unfold R' mL; rw [d]; exact_mod_cast (broken_charge (U:=U) (r:=r) (t:=ε)))) hx
 have ht:= mul_le_mul_of_nonneg_right hz (show 0 ≤ m' from Nat.cast_nonneg _)
 have ht':= mul_le_mul_of_nonneg_right hx' (show 0 ≤ mL from Nat.cast_nonneg _)
 obtain ⟨a,b⟩:=CF.Graph.oath B p U
 have hΔ: T ≥ β*(∑ x:Site n, -(PathData.atomSeries Z.cubic p U x + PathData.atomSeries Z.quartic p U x)) + ∑ x:Site n,-PathData.atomSeries Z.loop p U x:=by
    rw [sum_neg_distrib,sum_neg_distrib]; exact add_le_add (mul_le_mul_of_nonneg_left ((neg_le_neg (neg_le_of_abs_le a)).trans_eq (neg_neg _)) d') ((neg_le_neg (neg_le_of_abs_le b)).trans_eq (neg_neg _))
 rw [←dd]; change -(Z.principal q p β U) + κ*m'+ ξ*mL ≤ (-β*∑ b:Cell n,F b) + _ -- binder scope * consumes `+`? sums Lean notation encloses plus!
 unfold PathData.principal taxΔ; change -(β*((∑ b:Cell n,Y' b)+_)+_)+ κ*m'+ξ*mL ≤ (-β * ∑ b:Cell n,F b) + (T+_ -_ -_)
 rw [sum_neg_distrib,sum_neg_distrib] at hΔ; unfold ts tv at hr; unfold R' at hC; linarith only [mul_le_mul_of_nonneg_left hr d', ht,ht',hC,hΔ]

def cloak (T:Forest r)(F:Finset T.Free) (A:Support c) (Λ:Finset (Cell n)) (m:ℕ) := (room T F A m).filter (fun i=> untouched (face_anchors Λ) (Sequest m+Sequest m) i.val.1)
omit B
lemma cover_c : cloak T F A Λ m ⊆ room T F A m:=filter_subset ..
open Next.SectorChange
lemma enterCol (a:Finset T.Free)(h:a⊆cloak T univ A Λ m)(Y':LinkArray G (Blip T a))(C: LinkArray G a)(ht:0≤ ε)(t': broken r ε (T.drape (deep T a C Y')) = A) (g0:2*(r.count.val+1)<n.val) (p':suitedFee r.count.val ε≤v)(s:v≤R.c) : let t:= T.drape (deep T a C Y'); let x:=fun b:↥a=> G.plog (G.mat (C b)); let f:= stock T a x; let D:=myLog T a Y' A; ProbeBox f (2*v) ∧ ProbeBox (f+D) (2*v) ∧ TrustLogs (f+D) t r A v ∧ blank f r A (face_anchors Λ) m:=by
 intro t x f D
 let log_use (e:Bond n)(u:Working r A e) : G.chord (t e)≤v:= (purified ht (show _∉broken r ε t from t'.symm ▸ u.1) g0 u.2).trans p'; -- parse Proof? 
 let norm_use (e:Bond n)(u:Working r A e) : ‖logX t e‖≤2*v:= (R.sleeve _ ((log_use e u).trans s)).trans (mul_le_mul_of_nonneg_left (log_use e u) (by norm_num))
 have ht (b:↥a) : Working r A b.val.val:= kept_freed (A:=A) (m:=m) rfl ⟨b.val,cover_c (h b.property)⟩ -- implicit tune
 have hz(e:Bond n): collect G (f+D) e= (if Working r A e then logX t e else 0):=by
    change collect G (stock T a x) e+ collect G (myLog T a Y' A) e= _; rw [myLog_field]
    by_cases G0: ∀ i:↥a,e≠i.val.val
    · rw [stock_shallow x e G0,zero_add]; have hg:logX (T.drape (deep T a 1 Y')) e=logX t e:= by unfold logX t; rw [drape_agrees (X:=C) G0] -- might rewrites left
      rw [hg]; simp [G0]
    push Not at G0; obtain ⟨i,rfl⟩:= G0; rw [if_neg (show ¬(Working r A i.val.val ∧ ∀ j:↥a,i.val.val ≠ j.val.val) from fun p=> p.2 i rfl), stock_clean, add_zero,if_pos (ht _ )]; unfold x logX t; rw [drapeX]
 have v0:0 ≤ v:= ((by unfold suitedFee; positivity : 0 ≤ suitedFee _ ε).trans p')
 refine ⟨fun j=> ?_,fun j=> ?_,fun i u=> ?_,fun e pH=>?_⟩
 · by_cases t':∀ i:↥a,j≠i.val.val; · unfold f; rw [stock_shallow _ j t',norm_zero]; positivity
   push Not at t'; obtain ⟨b,rfl⟩:=t'; unfold f; rw [stock_clean,show x b=logX t _ from ?_]; exact norm_use b.val.val (ht b)
   unfold logX x t; rw [drapeX]
 · rw [hz]; split_ifs; rename_i he; exact norm_use _ he; rw [norm_zero]; positivity
 · exact ⟨(hz i).trans (if_pos u),log_use _ u⟩
 by_cases G0:∀ i:↥a,e≠i.val.val; · exact False.elim (pH (stock_shallow x e G0))
 push Not at G0; obtain ⟨b,rfl⟩:=G0; have hp:=mem_filter.mp (h b.property); exact ⟨(mem_filter.mp hp.1).2,hp.2⟩
end YM.Gleam
#print axioms YM.Gleam.at_shelf
#print axioms YM.Gleam.enterCol
