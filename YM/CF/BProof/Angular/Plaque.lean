import YM.CF.BProof.Angular.Draw

/-! Plaquette chord within the Mark bands: closed-tolerance price after testing. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Gauge Mag CF.BProof.Face SU MeasureTheory Wilson Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s : Side} (a x : Per s)(l:ℕ)(y:ℝ)(S:Hall s)(U:Config G s)(b:Eyes s)
variable {r m:ℝ} (he:l+1<s.val)(hu:0<l)

def Calm (q:ℝ): Prop := (∀ x p i, along a x<l→ group.chord (faceValue U (nf x p i))≤q) ∧ ∀ x p i, along a x≤l→ group.chord (faceValue U (hf x p i))≤q
lemma calm_move (q:ℝ) (t) : Calm a l U q=Calm a l (Lattice.gauge t U) q:=by unfold Calm; simp only [face_gauge,chord_conj]
include he
lemma calm_price (q t:ℝ)(W:Config G s)(h:Calm a l U q)(e:∀ p∈ washes a l,cd G (U p) (W p)≤t) : Calm a l W (q+4*t):= by
 have c(k:Lattice.Face (Per s))(H:group.chord (faceValue U k)≤ q)(x f g d:Bond s)(F:x ∈ washes a l)(L:f ∈ washes a l)(Z:g∈washes a l)(M:d∈washes a l)(v:∀ U : Config G s,faceValue U k=curl (U x) (U f) (U g) (U d)) : group.chord (faceValue W k)≤ q+4*t:=by
   apply le_trans (by simpa only [cd_one] using cd_triangle G 1 (faceValue U k) (faceValue W k)); refine add_le_add H ?_; rw [v W,v U]; exact (curl_bound ..).trans ((add_le_add (add_le_add (add_le_add (e x F) (e f L)) (e g Z)) (e d M)).trans (by linarith))
 constructor<;>intro x p i hx
 · have ht(x': Per s)(p:Space s)(h':along a x'≤l) : horiz x' p i∈washes a l:=by rwa [mem_wash,wet_h]
   have hv(p:Space s): vert x p∈washes a l:=by rwa [mem_wash,wet_v a _ he]
   exact c _ (h.1 x p i hx) _ _ _ _ (hv p) (ht (x+1) p (by rw [along_succ (by omega)]; omega)) (hv (p+tstep i)) (ht x p hx.le) (fun U=>nfc U x p i)
 have ht(p:Space s)(i:TAxis): horiz x p i∈washes a l:=by rwa [mem_wash,wet_h]
 exact c _ (h.2 x p i hx) _ _ _ _ (ht p (f₁ i)) (ht (p+tstep (f₁ i)) (f₂ i)) (ht (p+tstep (f₂ i)) (f₁ i)) (ht p (f₂ i)) (fun U=>hfc U x p i)
lemma calm_D (t:ℝ)(h:∀ p∈washes a l,cd G (mag y p) (U p)≤xi y)(hp:∀ i:TAxis,group.chord (comm y (f₁ i) (f₂ i)) ≤ t) : Calm a l U (t+4*xi y):=by
 apply calm_price a l (mag y) he t _ U _ h
 constructor <;> intro x p i hx
 · rw [nfc]; simp only [sheet,mag_h,mag_v,curl,one_mul,inv_one,mul_one,mul_inv_cancel, chord_one]; exact le_trans (group.chord_nonneg _) (hp i)
 rw [hfc]; exact hp i

include hu
lemma light_front (i:Bool)(h:Firm S.K (outlook a l S U b i) r m): sheet (formal a l S U b) (front a l i)= outlook a l S U b i:=by
 ext1 ⟨p,d⟩; unfold sheet; rw [horizontal_light]; unfold light profile
 cases i
 · simp_rw [front_left,along_self,angle_zero l hu (d:=0) (by simp)]; exact link_a S.K _ _ (h.pay _)
 simp_rw [front_right,along_add a (by omega : l<s.val), angle_one l hu (d:=l) (by omega)]; exact link_b S.K _ _ (h.pay _)
lemma sheet_light (i:Bool) : sheet (hall a l S U b) (front a l i)=outlook a l S U b i:=by rw [hall,outlook,V,sheet_gauge,inlet]; congr! 2; apply stage_set a _ U _ i _ hu (by omega) -- tune
lemma same_frame (h:∀ i,Firm S.K (outlook a l S U b i) r m) (p:Bond s)(hp:p∈ washes a l)(hh:p∉watches a l): hall a l S U b p=formal a l S U b p:=by
 rcases whichBond p with ⟨x,p,rfl⟩|⟨x,p,i,rfl⟩
 · rw [normal_light]; rw [watch_v a _ l p hu he] at hh; rw [mem_wash,wet_v a _ he] at hp; apply stage_normal a x _ U _ (by omega) hh
 rw [watch_h a _ _ p i] at hh; rw [mem_wash,wet_h] at hp; obtain ⟨g,hg⟩: ∃ g:Bool,x=front a l g:=by
   by_cases v:along a x=0
   · exact ⟨false, (along_zero.mp v).symm.trans (front_left a l).symm⟩
   refine ⟨true,?_⟩; have hv:= (add_along a x).symm; rw [show along a x=l by omega] at hv; exact hv
 subst x; exact congrFun ((sheet_light a l S U b he hu g).trans (light_front a l S U b he hu g (h g)).symm) (p,i)

abbrev qoriz := m+(4*S.K.bump/group.colorScale)*r^2
abbrev qnorm := S.K.C*((2/(l:ℝ))*(2*r))
-- abbreviations? implicit r m section - auto false
lemma calm_formal (h:∀ i,Firm S.K (outlook a l S U b i) r m)(hz:0≤r)(hr:r≤S.K.size) : Calm a l (formal a l S U b) (max (qoriz S (m:=m) (r:=r)) (qnorm (r:=r) l S)):=by
 let W(x: Per s):=sheet (formal a l S U b) x; have hp (x:Per s): W x=light a x l S U b:=funext fun ⟨p,i⟩=> horizontal_light a _ l S U b p i
 constructor <;> intro x p i hx
 · apply le_trans (b:=qnorm (r:=r) l S) _ (le_max_right ..)
   rw [nfc,normal_light,normal_light]; change group.chord (curl 1 (W (x+1) (p,i)) 1 (W x (p,i)))≤_
   unfold curl; rw [← cd_one,one_mul,inv_one,mul_one,← cd_mul_right G (W x (p,i)),one_mul,inv_mul_cancel_right]; rw [hp,hp,light,light,along_succ (by omega)] -- tune
   unfold profile; apply le_trans (link_step S.K _ _ _ _ (angle_mem ..) (angle_mem ..) ((h false).logs _) ((h true).logs _) hr); exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (angle_hop l hu _) (by positivity)) (zero_le_one.trans S.K.C_one)
 apply le_trans (b:=qoriz (m:=m) (r:=r) S) _ (le_max_left ..)
 rw [hfc]; change group.chord (CF.BProof.Face.read (W x) p i)≤_; rw [hp]; apply profile_square S.K _ _ _ (angle_mem ..) (h false) (h true) hr
lemma calm_N (h:∀ p∈watches a l, cd G (formal a l S U b p) (hall a l S U b p)≤xi y) (hp:∀ i,Firm S.K (outlook a l S U b i) r m) (hz:0≤r)(hr:r≤S.K.size): Calm a l U (max (qoriz S (m:=m) (r:=r)) (qnorm (r:=r) l S) + 4*xi y) := by
 rw [calm_move a _ U _ (V a l S U b)]
 apply calm_price a _ (formal a l S U b) he _ _ (hall a l S U b) (calm_formal a l S U b he hu hp hz hr)
 intro p H; by_cases hv:p∈ watches a l
 · exact h p hv
 rw [same_frame a l S U b he hu hp p H hv,cd_self]; exact (coin_pos ..).le
end YM.CF.BProof.Angular
