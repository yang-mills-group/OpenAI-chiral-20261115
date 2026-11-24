import YM.CF.BProof.Gates.Sized

/- Torus sizes, cost gates include L_Q/s and F/c. supply at all matching periods,
including optional (used later) sufficiently large mesh ratios etc. not using wrong N lattice.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates.Stage
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing
open scoped Topology BigOperators Classical MatrixOrder Matrix
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}
variable (S:Gates.Stage c w R v) (L s:Side) (a:ℕ)(y:ℝ)(W:ℕ)
def LQ := LP L y+2*L.val
lemma LQ_pos : 0<LQ L y:= Nat.add_pos_left (PP ..) _
-- conditions on Nat.
structure Tori (s:Side) : Prop where
  grid : LQ L y∣s.val
  size : 4≤s.val/LQ L y
  periods : 2^(r_P L y+1)∣ (s.val/LQ L y)
  fit : 2*LP L y ∣ s.val
  face : gF y S.scene.size ∣ s.val
  wide : 4 ≤ s.val/gF y S.scene.size
  light : W∣s.val
  well : 4≤ s.val/W

variable (P: Entice S L a W y)
private lemma appoint (d: ℕ)(hl:0<d)(v:d∣ s.val)(b:4≤ s.val/d): ∃ c:Side,∃ g:Ratio c s,c.val=s.val/d ∧ g.count.val=d:=by
 let c:Side:=⟨s.val/d,by omega⟩; refine ⟨c,⟨⟨d,hl⟩,?_⟩,rfl,rfl⟩; exact (Nat.div_mul_cancel v).symm
include P
lemma qualify (h:Tori S L y W s)(u:2*L.val∣a) : Nonempty (Setup S L a s W y):=by
 obtain ⟨d,k,hv,he⟩:= appoint s (LQ L y) (LQ_pos ..) h.grid h.size; let e:=DP L a y; have hp:=P.wide
 obtain ⟨x,g,hF,hx⟩:= appoint s (gF y S.scene.size) (Gates.posF ..) h.face h.wide
 obtain ⟨x',g',hD,h'⟩:= appoint s W (lt_of_lt_of_le (Gates.least_p c (Stage.M S) R (gap L a) y S.F ..) P.choice) h.light h.well
 let p:Bands s L a (LP L y):= {q:=d,grid:=k, long:= e,short:=gap L a,pivot:=a,total:= ?_,enough:=hv.symm ▸ h.size, long_pos:=by unfold e; omega, short_pos:=GP L a,left:=rfl,multiplesW:=u, gap_len:=rfl,band_len:=P.rise, powP:=rfl, rP:=r_P L y, rP_pos:=P.Ppos, dyadicH:=hv.symm ▸ h.periods, slotsH:=h.fit} -- commas within by semicolon tune
 exact ⟨p,x,hF.symm ▸ h.wide,g,hx,x',g',h',hD.symm ▸ h.well⟩ -- tune ? order
 rw [he]; unfold LQ; rw [← P.rise]; unfold e gap; omega
-- always available. fixed s divisible sufficiently many, arbitrarily large. λ≥.. W>0. No connection to Fits? leaf picks periods at fixed level.
def win := 2^(r_P L y+1)*LQ L y
omit P in
lemma win_pos : 0<win L y:= mul_pos (pow_pos (by decide) _) (LQ_pos ..)
def require := win L y*(2*LP L y)*gF y S.scene.size*W
lemma layout (s:Side)(h:4*Stage.require S L y W∣s.val) : Tori S L y W s :=by
 let t:= LQ L y; have ht:0<t:=LQ_pos ..; have he:= P.choice; let T:=Stage.require S L y W; let Q:=win L y; have hf:0<W:=lt_of_lt_of_le (Gates.least_p ..) P.choice; have hy:=win_pos L y; have hY:=PP L y; have hx:=posF y S.scene.size; have vp:0<Q:=hy
 have hc(j:ℕ)(hq:j∣T)(v:0<j): j∣ s.val ∧ 4≤ s.val/j:=by
    have hp:4*j∣s.val:=dvd_trans (mul_dvd_mul_left _ hq) h; exact ⟨dvd_trans (dvd_mul_left ..) hp,(Nat.le_div_iff_mul_le v).2 (Nat.le_of_dvd s.property hp)⟩
 have hQ:Q∣ T:= dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right ..) _) _
 have ⟨x,y₁⟩:=hc t (dvd_trans (dvd_mul_left ..) hQ) ht; have ⟨A,a⟩:=hc (gF y S.scene.size) (dvd_mul_of_dvd_left (dvd_mul_left ..) _) hx; have ⟨B,b⟩:= hc W (dvd_mul_left ..) hf
 refine ⟨x,y₁,?_,(hc _ (show 2*LP L y∣ T from dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left ..) _) _) (by positivity)).1,A,a,B,b⟩
 obtain ⟨k,v⟩:= (hc Q hQ vp).1; refine ⟨k,?_⟩; rw [v]; change (2^(r_P L y+1)*t*k)/t=_; rw [mul_right_comm,Nat.mul_div_left _ ht]
end YM.CF.BProof.Gates.Stage
