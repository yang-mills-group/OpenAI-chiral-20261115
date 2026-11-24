/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Gleam.Farther
import YM.Next.RANK.Ray
import YM.Next.FLUCTUATIONS.Charts
import YM.Work.F03.Transport
/-! # Angular comparison through true plaquette curvatures at every kept spatial row. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{v t:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:fieldDir G n 1} {R:Rules G}
local notation "u" => collect G X -- remove ambiguous variable names
private lemma stroll_edge (a : Step) (x:Site n) : separation x (x+a.vec)≤1 ∧ separation x (a.used x).1≤1 ∧ separation x ((a.used x).1+step (a.used x).2)≤1 :=by
 obtain ⟨a,b|b⟩:= a; · exact ⟨step_towards ..,by simp [Step.used],step_towards ..⟩
 have he(x : Site n): separation x (x-step a)≤1:= by rw [separation_comm]; have hp:= step_towards (n:=n) (x-step a) a; rw [show x-step a+step a=x by abel] at hp; exact hp
 simpa only [Step.used,Step.vec,↓reduceIte,sub_add_cancel,←sub_eq_add_neg] using And.intro (he x) ⟨he x,(show separation x x≤1 by simp)⟩
def Working (r:Ratio c n)(A:Support c)(b:Bond n) : Prop := r.parent b.1∉A ∧ InHouse r (r.parent b.1) b
def TrustLogs (X:fieldDir G n 1)(U:Config G n)(r:Ratio c n) (A: Support c)(v:ℝ):=∀ b:Edge (Site n), Working r A b → collect G X b=G.plog (G.mat (U b)) ∧ G.chord (U b)≤v
private lemma approach_walk (h:TrustLogs X U r A v) (p:0≤v)(t':v≤R.c)(l:Walk)(k:Safe r A l.length x) :
   G.chord (travel U x l) ≤ l.length*v ∧ ‖G.curvature (travel U x l)-linkSum u x l‖≤(G.colorScale*l.length^2+R.C*l.length)*v^2 :=by
 induction l generalizing x with
 | nil=> simp [travel,linkSum]
 | cons a l ih=>
    let i:=x+a.vec; obtain ⟨hs,hb,hc⟩:= stroll_edge a x; have hv(a':Site n)(f:separation x a'≤1):r.parent a'=r.parent x:= k.2 a' (by change _≤ l.length+1; omega)
    have hx:Safe r A l.length i:= k.shift ((Nat.add_le_add_right hs l.length).trans (by rw [List.length_cons,add_comm]))
    let y:=a.used x; let D:=G.colorScale; let L:ℝ:=l.length; let W:=a.read U x; let z:= (if a.neg then - u y else u y); let Y:=travel U i l
    obtain ⟨f',p'⟩:= h y (by have hb:r.parent y.1=r.parent x:= hv _ hb; unfold Working InHouse; rw [hb, hv _ hc]; exact ⟨k.1,rfl,rfl⟩)
    have he:G.chord W ≤ v:=by unfold W Step.read; split_ifs; rw [G.chord_inv]; exact p'; exact p'
    have hu: ‖G.curvature W-z‖ ≤ R.C*v^2:= by
       rw [show ‖G.curvature W-z‖ = ‖G.plog (G.mat (U y))-G.curvature (U y)‖ by unfold W z Step.read; split_ifs <;> rename_i h' <;> rw [f']; rw [G.curvature_inv]; congr 1; unfold y; abel; rw [norm_sub_rev]] -- split semicolon grouping
       exact (R.bars _ (p'.trans t')).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (G.chord_nonneg _) p' _) R.positive.le)
    obtain ⟨h1,h2⟩:=ih (x:=i) hx
    change _ ≤ L*v at h1; change _ ≤(D*L^2+ R.C*L)*_ at h2
    rw [List.length_cons,Nat.cast_add,Nat.cast_one]; change G.chord (W*Y)≤(L+1)*v ∧ ‖G.curvature (W*Y)-(z+linkSum u i l)‖≤ _
    constructor
    · exact (G.chord_triangle ..).trans ((add_le_add he h1).trans_eq (by ring))
    have hl: ‖G.curvature (W*Y)-(G.curvature W+ G.curvature Y)‖ ≤ D*v*(L*v):= (weave W Y).trans (mul_le_mul (mul_le_mul_of_nonneg_left he G.colorScale_pos.le) h1 (G.chord_nonneg _) (mul_nonneg G.colorScale_pos.le p))
    apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (G.curvature W+ G.curvature Y) _); rw [show G.curvature W +_-(z+linkSum u i l) = (G.curvature W-z)+(G.curvature Y-linkSum u i l) by abel]; apply (add_le_add hl ((norm_add_le ..).trans (add_le_add hu h2))).trans
    have hb:0 < D:= G.colorScale_pos; have hx:0 ≤ L:= Nat.cast_nonneg _; change D*v* _ + (_+_)≤(D*(L+1)^2+ R.C*(L+1))*v^2; nlinarith only [mul_nonneg hb.le (sq_nonneg v),mul_nonneg hx (mul_nonneg hb.le (sq_nonneg v))]
private lemma faceSum (b:Cell n) : faceCurl b X = linkSum u b.1 (square b.2.val.1 b.2.val.2):= (fundamental ..).symm
abbrev faceCutError (R:Rules G) (v:ℝ):= (G.colorScale*16+ R.C*4)*v^2
lemma angleFaceSmall (h:TrustLogs X U r A v) (p:0≤v)(t':v≤R.c)(b: Cell n)(k:Safe r A 4 b.1) :
    G.chord (faceValue U b) ≤ 4*v ∧ ‖G.curvature (faceValue U b)-faceCurl b X‖ ≤ faceCutError R v:=by
 rw [faceSum]; let l:=square b.2.val.1 b.2.val.2; obtain ⟨f,g⟩:= approach_walk h p t' l k; rw [show l.length=4 from rfl,Nat.cast_ofNat] at f g; exact ⟨f,g.trans_eq (by unfold faceCutError; ring)⟩
-- future ellLine comparisons
lemma grantPath (v : ℝ) (o x:Site n)(f:Walk)(h:∀ b:Edge (Site n),separation o b.1≤m → ‖collect G X b‖≤v) (k:separation o x+ f.length≤m): ‖linkSum u x f‖ ≤ f.length*v:=by
 induction f generalizing x with
 | nil=> simp [linkSum]
 | cons a l ih=>
    obtain ⟨e,H,_⟩:= stroll_edge a x; rw [List.length_cons] at k ⊢
    have hL:= h (a.used x) (by apply (separation_triangle o x _).trans; omega)
    let B:G.Color:= if a.neg then - (collect G X) (a.used x) else (collect G X) (a.used x)
    have hs:‖B‖ ≤ v:=by unfold B; split_ifs; rw [norm_neg]; exact hL; exact hL
    have ht:separation o (x+a.vec)+l.length≤m:= by have h:=separation_triangle o x (x+a.vec); omega
    calc
     _ ≤ ‖B‖+‖linkSum u (x+a.vec) l‖:= norm_add_le ..
     _ ≤ v+l.length * v:= add_le_add hs (ih _ ht)
     _ =_:= by push_cast; ring
lemma grantFace {k:Cell n}(h:∀ b:Edge (Site n), separation o b.1≤m → ‖collect G X b‖≤v)(t:separation o k.1+4≤m): ‖faceCurl k X‖ ≤ 4*v:= by rw [faceSum]; exact (grantPath v o k.1 (square k.2.val.1 k.2.val.2) h t).trans_eq (by rw [show List.length _ =4 from rfl,Nat.cast_ofNat])
abbrev slotError (R:Rules G)(k:ℕ)(v:ℝ) := faceCutError R v +8*G.colorScale*k*v^2
lemma grantSlot (h:TrustLogs X U r A v) (p:0 ≤ v)(t':v ≤ R.c)(w:RG.Slot)(k:Safe r A (m+4) x)(q:w.length≤m): ‖w.atSite U x-faceCurl (slotFace w x) X‖ ≤ slotError R m v:=by
 let i:=slotFace w x; let s:= travel U x w.walk; let H':=G.colorScale; let D:= G.curvature (faceValue U i)
 have hp:= k.shift (e:=4) ((Nat.add_le_add_right (Work.E04.slot_separation w x) 4).trans (Nat.add_le_add_right q _)); have hz: w.walk.length ≤ m:= (Nat.le_add_right ..).trans q; have hs:G.chord s≤ m*v:= (approach_walk h p t' w.walk (k.shift (by simp; omega) : Safe r A w.walk.length x)).1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hz) p)
 obtain ⟨e,g⟩:= angleFaceSmall h p t' i hp
 have hx:‖G.adjoint s D-D‖ ≤ 2*H'*(m*v)*(4*v):=(Next.Fluctuations.adjoint_norm_sub ..).trans (mul_le_mul (mul_le_mul_of_nonneg_left hs (by have v:=G.colorScale_pos; change 0≤2*G.colorScale; positivity)) ((G.curvature_norm _).trans e) (norm_nonneg _) (by unfold H'; have e:=G.colorScale_pos; positivity))
 rw [atSite_path]; apply (norm_sub_le_norm_sub_add_norm_sub _ D _).trans; refine (add_le_add hx g).trans_eq ?_; unfold slotError; unfold H'; ring
end YM.Gleam
#print axioms YM.Gleam.grantSlot
