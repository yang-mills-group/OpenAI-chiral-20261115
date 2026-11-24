import YM.CF.BPress.Wealth.Regime
/-! Support of `eq:B-Taylor` in pulling all native slots, and direct assertion. Noise is in physical links; no derivative of sectors. All bool tests allowed computed even from fallback U; conclusion of heavy charges uses valid proofs of Tested(w,U), holds exactly on noisy physical links. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side} {κ y C D:ℝ}

-- per-root needed input property (`h=Mission...,H.relevant...` supplies). support expressed only by Depot tickets of chosen root. for direct ANY pulled orientation from this use
structure Tested (D κ y:ℝ)(S : Finset (Link s))(U:Micro s)(w:Directions group s): Prop where
 angle (i:Link s): ‖w i‖ ≤ D*temp y
 small (i:Link s): i ∈ S → chord (U i) (background y i) ≤ xi y+κ*temp y
 near (i:Link s): i ∈ S → chord (U i) (actuated y w i) ≤ xi y
lemma license {b:BandWidth}{X:Bands s b}{M:ℕ}{i:Root s} (h:retained X M i)(p: High b M){K:Bills X E}{U V:Micro s} (t:Mission X y K V U)(v: ToneNoise y V)(x: Dividend D κ C y)(f:regular (X:=X) (M:=M) (chosen X κ y K) i)(q:Sheet.Atlas)(w:κ*temp y < q.δ)(l:q.C*κ ≤ D)(u:0≤D): Tested D κ y (tickets M i) U (canon X (softAl X κ y K q)):=by
 have he:= temp_pos x.young; refine ⟨fun z=> raw_le (mul_nonneg u he.le) (softAl X κ y K q) (fun j=>?_) z,fun z g=> costs_soft X M t v h p x.branch f z g,fun z g=> tests_soft X M q t v h p w f z g⟩ -- tune order
 refine (soft_bounds κ y q w x.branch K j).trans ?_; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right l he.le
variable (q:Dividend D κ C y) (t:Signed)
include q
lemma mA_small : C*mA y≤ temp y:=by have hx:=xi_pos q.young; linarith only [q.buyer,q.branch,hx]
private lemma m_le : aA y*mA y≤ finer y:=by
 unfold finer; have he:= xi_pos q.young; have hp:= q.mag; have ht:=aA_positive q.young; nlinarith [sq_nonneg (temp y)]
lemma finer_aA : aA y^3 ≤ finer y:=by rw [pow_succ,aA_sq q.young,mul_comm]; exact m_le q

variable {U : Micro s}{w : Directions group s}
lemma back_flag (i:Bonding s): group.chord (faceR t (background y) i) ≤ temp y:= (q.bgChord s t i).trans (mA_small q)
lemma drawn_flag (i:Bonding s)(h:∀ j:Fin 4,chord (U (address t (aperture i j))) (background y (address t (aperture i j)))≤ xi y+κ*temp y): group.chord (faceR t U i) ≤ temp y:= by
 rw [←chord.one]; refine (chord.triangle _ (faceR t (background y) i) _).trans ((add_le_add (item_close t U _ _ _ h) ((chord.one ..).le.trans (q.bgChord s t i))).trans q.buyer)
omit q
-- square-form perturbation, real inner product. X: exact background vec not norm; w~D. r epsilon sum. prove with triangular/CS.
lemma volumeQ {F:Type*}[NormedAddCommGroup F][InnerProductSpace ℝ F] {x y w z:F}{k r:ℝ}(p:‖x‖ ≤ k)(t:‖y‖ ≤ k)(v:‖w‖ ≤ k)(h:‖x-z‖ ≤ r)(b:‖y-x-w‖ ≤ r):
 |(‖y‖^2/2) -(‖x‖^2/2+ inner ℝ z w+‖w‖^2/2)| ≤ 3*k*r:=by
 have hm:= (norm_nonneg x).trans p; have hr:0≤r:=(norm_nonneg _).trans b; have hb:‖x+w‖ ≤ 2*k := by apply le_trans (norm_add_le ..); linarith
 have ht:= abs_real_inner_le_norm (x-z) w; rw [inner_sub_left] at ht; have ht: |inner ℝ x w-inner ℝ z w| ≤ r*k:= ht.trans (mul_le_mul h v (norm_nonneg _) hr)
 have hh: |‖y‖-‖x+w‖|≤ r:=by refine (abs_norm_sub_norm_le ..).trans ?_; rwa [← sub_sub] -- tune sub_sub not identity?
 have he: |‖y‖^2-‖x+w‖^2| ≤ 3*k*r:= by
    rw [sq_sub_sq, abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm (_+_)]; calc
     _ ≤ r*(3*k):= mul_le_mul hh (show ‖y‖+‖x+w‖ ≤ 3*k by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _)) hr
     _ ≤ 3*k*r := Eq.le (by ring)
 rw [norm_add_sq_real] at he; rw [abs_le] at *; constructor <;> nlinarith only [he.1,he.2,ht.1,ht.2,hb, mul_nonneg hm hr] -- tune won't press hb redundant

lemma psi_norm (t:Signed){U:Directions group s}{K:ℝ}(p:∀ i:Link s, ‖U i‖ ≤ K) (x:Bonding s): ‖orbitP t x U‖ ≤ 4*K:=by
 have v:0≤K:=(norm_nonneg _).trans (p (0,0)); apply p_norm _ ((pi_norm_le_iff_of_nonneg v).mpr _); intro i; rw [brandW,orbit_fee]; exact p _
variable (d:Clip) (p : BudgetPoint) (β:ℝ)(g:0≤β)
-- Q written in native W. below use W=g*w; currently terms contain β directly.
def Lp (W:Directions group s)(x:Bonding s):= β*d.direct* inner ℝ (mA y • psi 1 x.2) (orbitP 1 x W)
def Qp (W:Directions group s)(x:Bonding s):= β*d.direct* ‖orbitP 1 x W‖^2/2
include q g
lemma income_direct (x:Bonding s)(v:p.threshold=temp y)(z:0≤ D)(t:∀ j, chord (U (aperture x j)) (background y (aperture x j)) ≤ xi y+κ*temp y) (h:∀ j, chord (U (aperture x j)) (actuated y w (aperture x j)) ≤ xi y)(k:∀ i, ‖w i‖ ≤ D*temp y):
 |hide d p β U x - (hide d p β (background y) x + Lp (y:=y) d β w x + Qp d β w x)| ≤ β*(d.direct * (3*(1+4*D)*C)) * finer y * temp y:=by
 -- at identity orientation
 have he(X:Micro s): faceR 1 X x=faceValue X x:=by rw [faceR,pull_id]
 let P:= canonM (faceR 1 (background y) x); let W:= canonM (faceR 1 U x); let Z:= orbitP 1 x w; let D':=canonE Z; let f:=(1+4*D)*temp y; let A:= psi 1 x.2
 have ht: group.chord (faceR 1 U x) ≤ temp y:= drawn_flag q 1 x (fun j=>by rw [addr_id]; apply t); have h0:=temp_pos q.young; have hp:temp y≤ f:= le_mul_of_one_le_left h0.le (by linarith)
 have hv: ‖P‖ ≤ temp y:= by rw [show ‖P‖=_ from canonM_price _]; exact back_flag q 1 x
 have hW: ‖W‖ ≤ temp y:=(canonM_price ..).le.trans ht
 have hZ: ‖canonE Z‖≤f:=(canonE.norm_map _|>.le).trans ((psi_norm 1 k x).trans (Eq.trans_le (by ring : 4*(D*temp y)=(4*D)*temp y) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) h0.le)))
 have hb:‖P-canonE (mA y • A)‖≤ C*finer y:=by rw [map_smul]; exact (q.bgCase ..).trans (mul_le_mul_of_nonneg_left (finer_aA q) q.posC.le)
 have hL:= q.faceCase s 1 U x w (fun i=>k _) (fun i=> by rw [addr_id]; exact h i)
 have h':= volumeQ (hv.trans hp) (hW.trans hp) hZ hb hL; rw [canonE.inner_map_map,canonE.norm_map] at h'; unfold hide hideH PathData.clipped Lp Qp; rw [v, ←he,← he (background y),if_pos ht, if_pos (back_flag q 1 x),←canonM_price,←canonM_price]; refine le_trans ?_ (le_trans (a:= (β*d.direct)*_) (mul_le_mul_of_nonneg_left h' (by positivity [d.quadratic_pos])) ?_); -- tune
 · unfold W P Z A; rw [←abs_of_nonneg (mul_nonneg g d.quadratic_pos.le),←abs_mul]; apply Eq.le; congr 1; rw [abs_of_nonneg (mul_nonneg g d.quadratic_pos.le)]; ring
 unfold f; exact Eq.le (by ring)
end YM.CF.BPress.Wealth
