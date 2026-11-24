import YM.CF.Buffered.Capstone
/-! # Scalar weights on these tiles

Ticket at horizontal size and horizon with β (heat) & clip & B modified table
prices. No implicit extension costs assumed, split exactly as in pressure lemma.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Gloss Scroll Spire Push.SectorMeasure Ordered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m p v w l B n:Side}
local notation "D" => Domain m B
local notation "qM" => GridN m
local notation "I" => Xmind m B
local notation "X" => Pack m B
local notation "S" => Locale v B
local notation "N" => CSide v B
local notation "d" => Domain v B
local notation "g" => GridN v

-- input pin(t), Λ privileges issued above, e and x flag tolerance.
structure Ticket (m v B p:Side) (e x:ℝ) where
 K: Ordered m v p
 pin: Pinning m B
 c: Phase.Part m B
 W: Scroll m B c
 uv:ℝ
 fv:ℝ
 E: ScaleK uv fv W
 stamp:ℝ
 pad: Budget B e stamp
variable {e x : ℝ}
namespace Ticket
variable (b:Ticket m v B p e x)(F:Pack m B)(w: Locale v B) (r:Rail (Uniform p))
variable (q:Clip) (β:ℝ)

def tabV (i:Tor g) (w:S):= tab b.pin b.W (b.K.pebbles.zone 0 i.val) (whole b.K w)
def paintI (i:Post N)(w:S):= b.K.canvas 0 i (whole b.K w)
def seedM (i:Post N)(w:S): FC Spin := (permitted b.K e x).indicator (fun z=> Mil.seed (paintI b i z)) w

lemma paint_reads (i: Post N) : paintI b i (reel r (b.K.fromCube F))=b.K.canvas r i F:=by
 let y:= onPack B (b.K.ferry 0 r ∅) F
 have he:b.K.canvas 0 i y= b.K.canvas r i F:=by rw [show b.K.canvas 0 i y=b.K.canvas r (shades ∅ i) F from color_turned ..,show shades ∅ i=i from Subtype.ext (funext fun j=>by simp [shades])]
 rw [paintI,←he]; apply canvas_eq; rw [whole_zero]; exact (ferry_none ..).symm
lemma tab_reads (i:Tor g)(u:F∈secure e x): tabV b i (reel r (b.K.fromCube F))=tab b.pin b.W (b.K.pebbles.zone r i.val) F:=by
 let y:= b.K.ferry 0 r ∅
 let z:= reel r (b.K.fromCube F)
 have he:= tab_turn b.K b.pin b.W 0 r i F ∅
 change tab _ _ _ (onPack B y F) = _ at he; rw [nom_r, Spire.payZ,η_x _ (show ∀ i, y.glare i=false from fun i=>by simp [y,ferry,maskC])] at he
 exact (tab_eq b.K b.pad b.pin b.E i 0 (tallyP ((permitted_iff b.K ..).1 ((permit_iff ..).1 u r)).1) (dominated y F (tallyP u.1)) (by rw [whole_zero]; exact (ferry_none ..).symm)).trans he
lemma tab_pays (i:Tor g): Envelope ((permitted b.K e x).indicator (tabV b i)) :=by
 have he:= (pays b.pad b.pin b.E (b.K.pebbles.zone 0 i.val)).comp (whole_cont b.K).continuousOn fun z (v:z∈permitted b.K e x)=>tallyP ((permitted_iff ..).mp v).1
 obtain ⟨K,h⟩:= tab_bound b.pad b.pin b.E (b.K.pebbles.zone 0 i.val); exact env_piece _ (allowed_borel b.K e x) he K fun i u=> h _ (tallyP ((permitted_iff ..).1 u).1)

lemma tab_refl (i:Tor g)(s:Axis)(u:w∈permitted b.K e x) : tabV b i (Rails.past {s} w)=star (tabV b (shades {s} i) w) :=by
 let y:=b.K.ferry 0 0 {s}
 let z:=whole b.K w
 have ht: z∈secure e x:= (permitted_iff ..).1 u
 have he:= tab_turn b.K b.pin b.W 0 0 i z {s}
 change tab _ _ _ (onPack B y z)=_ at he; rw [Spire.payZ, show Spire.wageZ (phat y)=true from ?_] at he -- tune
 · apply Eq.trans _ (show _=_ from he)
   apply tab_eq b.K b.pad b.pin b.E i 0 _ (dominated y _ (tallyP ht.1)); swap
   · apply tallyP ((permitted_iff ..).mp ((turn_permit ..).2 u)).1
   rw [whole_zero]; change _ = reel 0 (b.K.fromCube (onPack _ _ z)); unfold z; rw [ferry_extract,whole_zero]
 unfold Spire.wageZ; change false.xor (detX (glazed (maskC {s})))=_; rw [mirror_mask,det_t]; rfl
lemma seedI (i:Post N){z:S}(p:z∈permitted b.K e x): seedM b i z=Mil.seed (paintI b i z):= Set.indicator_of_mem p _
lemma seedP (i:Post N){z:S} (r:z∈permitted b.K e x): ‖paintI b i z‖=1:= unit_canvas b.K b.pad _ _ ((permitted_iff ..).1 r)
lemma seed_turn (i: Post N)(s:Axis): seedM b i (Rails.past {s} w)=theta (mirrorSpin s) (seedM b (shades {s} i) w):=by
 by_cases p:w∈permitted b.K e x
 · have he:= Mil.seed_turn s _ (b.seedP (shades {s} i) p); rw [seedI b _ p, he,seedI b _ ((turn_permit ..).2 p)]; apply congrArg; rw [show Rails.past {s} w= reel 0 (b.K.fromCube (onPack B (b.K.ferry 0 0 {s}) (whole b.K w))) from (by rw [ferry_extract,whole_zero]), paint_reads,color_turned]; rfl
 unfold seedM; rw [Set.indicator_of_notMem p, Set.indicator_of_notMem (fun h=>p ((turn_permit ..).1 h)), theta_zero]
lemma seed_pays (i:Post N) : Envelope (seedM b i) := by
 let U : Set S :=permitted b.K e x
 let uX:= b.K.spirit B|>.zone 0 i.val; let Q := Mil.side uX
 let V(v:S): Op Spin:=localPair (paintI b i v)
 have he(v:S): V v=(Phase.pair m B (whole b.K v).1 (whole b.K v).2).submatrix Q Q:=by
    ext k l:1; unfold Phase.pair bow Cfield; simp only [Matrix.submatrix_apply]; rw [jump_apply,if_pos (show Equiv.refl _ (Q k).1=(Q l).1 from rfl)]; rfl
 have hw : Continuous (fun A: Op (Xmind m B)=> A.submatrix Q Q):= by exact continuous_matrix fun i j=> continuous_id.matrix_elem _ _ -- tune
 have hp := hw.comp_continuousOn ((pair_cont b.pad.1).comp (whole_cont b.K).continuousOn fun x (j:x∈U)=>tallyP ((permitted_iff ..).1 j).1)
 -- use env_piece on pair then seed continuous
 have hu : ContinuousOn V U:= hp.congr fun x _=> he x -- check
 obtain ⟨K,h⟩:= (show Envelope (fun x:(Metric.closedBall (0:Op Spin) 1)=> seedR above x.val) from Env.compact ((continuous_seed above).comp continuous_subtype_val)).cost
 refine env_piece U (allowed_borel ..) ((continuous_seed above).comp_continuousOn hu) K fun v u=> h ⟨V v,Metric.mem_closedBall.mpr ?_⟩; rw [dist_zero_right]; unfold V; exact (CStarRing.norm_of_mem_unitary (localPair_mem _ (b.seedP i u))).le

-- split with real sqrt (rpow ½^faces), no logs in measurability.
def sumBill (w:S) := ∑ i:Tor g, i.share • tabV b i w
def priceF (w:S) := ∑ a:PlaqAxes,∑ i:Roost d (Facade.frame a), i.share * coinF q (Facade.detail a i w)
def drizzle (w:S) := ∏ i: Tor g, small b.K i w ^ i.share
def portion (w:S) := ((b.drizzle w:ℝ):ℂ)*Complex.exp (-((β:ℂ)*(priceF q w:ℝ))-sumBill b w)
def deck:= (permitted b.K e x).indicator (portion b q β)
lemma sum_ok : Envelope ((permitted b.K e x).indicator b.sumBill) :=by
 let p : Set S :=permitted b.K e x; have he(i:Tor g):Envelope fun w':S=> i.share • p.indicator (tabV b i) w':= Girt.pole_w _ (fun z:ℂ=> i.share • z) (continuous_id.const_smul i.share) (b.tab_pays _)
 rw [show (permitted (B:=B) b.K e x).indicator b.sumBill=(fun z=>∑ i:Tor g,i.share • p.indicator (b.tabV i) z) from ?_]
 · exact Env.total univ he -- tune
 funext z; by_cases h:z∈p; rw [Set.indicator_of_mem (show z∈permitted b.K e x from h)]; simp only [Set.indicator_of_mem h,sumBill]
 rw [Set.indicator_of_notMem (show z∉permitted b.K e x from h)]; simp only [Set.indicator_of_notMem h,smul_zero,sum_const_zero]
open scoped Matrix.Norms.Frobenius in
include b in
lemma price_ok : Envelope (priceF (v:=v) (B:=B) q):=by
 apply Env.compact
 -- native residual on repeat, analytic continuity. OR surplus cont (Frobenius norm issues).
 let z:S→ X:= whole b.K; have ht(i:Face (Per D)): Continuous (fun x:X=> coinF q (faceValue x.1 i)):=by
   let A(x:X):=energyF q (faceValue x.1 i)
   have hp:Continuous A:=Continuous.sub (by change Continuous fun x:X=> SU.group.price (travel x.1 _ _); fun_prop) (Continuous.mul continuous_const (by change Continuous fun x:X=>WilsonStartup.residual SU.group i x.1; simp_rw [WilsonStartup.residual,← Quad.surplus_actual]; exact Quad.surplusMat_diff (G:=SU.group)|>.continuous.comp (SU.group.continuous_mat.comp ((Wilson.continuous_travel ..).comp continuous_fst))))
   let E(x:X): X:= (Reef.echo x.1,x.2); have he:Continuous E:=by unfold E; exact (continuous_pi fun j:RZ m B=> Reef.icyC.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
   unfold coinF; simp_rw [←show ∀ x:X,faceValue (E x).1 i=Reef.qG (faceValue x.1 i) from fun x=>Reef.echo_t ..]; exact (hp.add (hp.comp he)).div_const _
 apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro j _; refine Continuous.mul continuous_const ?_; have hh(w:S): Facade.detail i j w=faceValue (z w).1 ((b.K.sugar B).zone 0 j.val,i):=by nth_rw 1 [←whole_zero b.K w]; exact Facade.intrinsic ..
 simp_rw [hh]; exact (ht _).comp (whole_cont b.K)
lemma drizzle_ok : Envelope b.drizzle:= by apply Env.compact; exact continuous_finsetProd _ fun i _=> (water_continuous b.K _).rpow_const (fun w=> Or.inr i.share_pos.le)
lemma deck_ok : Envelope (deck b q β):=by
 let f:= (permitted b.K e x).indicator b.sumBill
 rw [show deck b q β=(permitted b.K e x).indicator (fun x=> ((b.drizzle x:ℝ):ℂ)*Complex.exp (-((β:ℂ)*(priceF q x:ℝ))-f x)) from ?_]
 · refine env_indicator _ (allowed_borel b.K e x) (env_mult (Girt.pole_w _ _ Complex.continuous_ofReal b.drizzle_ok) (Girt.kitE _ _ (fun (x:ℝ)(y:ℂ)=>Complex.exp (-((β:ℂ)*(x:ℝ))-y)) (by fun_prop) (b.price_ok q) b.sum_ok))
 apply Set.indicator_congr; intro y t; unfold portion f; dsimp only; rw [Set.indicator_of_mem t]
lemma deck_star (i:Axis): deck b q β (Rails.past {i} w)=star (deck b q β w):= by
 by_cases hp:w∈permitted b.K e x; swap; · unfold deck; rw [Set.indicator_of_notMem (fun h=>hp ((turn_permit ..).1 h)),Set.indicator_of_notMem hp,star_zero]
 unfold deck; rw [Set.indicator_of_mem hp,Set.indicator_of_mem ((turn_permit ..).2 hp)]; let T:=Rails.past {i} w
 have he:drizzle b T=b.drizzle w:=by unfold T drizzle; symm; rw [←Equiv.prod_comp (mirrorR {i}) (fun x=> (small b.K x w)^x.share)]; refine prod_congr rfl fun j _=>?_ ; rw [mist_turn, show (mirrorR {i}) j=shades {i} j from rfl,share_mirror]
 have hu:priceF q T=priceF q w:=by refine sum_congr rfl fun a _=>?_ ; unfold T; symm; rw [←Equiv.sum_comp (mirrorR {i}) (fun j=>j.share * coinF q (Facade.detail a j w))]; refine sum_congr rfl fun j _=>?_ ; rw [show (mirrorR {i}) j= _ from (show mirrorR {i} j=shades {i} j from rfl), share_mirror, price_turn b.K _ _ _ (coin_s q)]
 have hv:b.sumBill T=star (b.sumBill w):=by unfold sumBill; rw [←Equiv.sum_comp (mirrorR {i}) (fun j=> j.share • b.tabV j w),star_sum]; refine sum_congr rfl fun j _=>?_ ; unfold T; rw [tab_refl b w j i hp, show mirrorR {i} j=shades {i} j from rfl,share_mirror,star_smul,show star j.share=j.share from star_trivial _]
 unfold portion; rw [he,hu,hv,Complex.star_def,map_mul,←Complex.exp_conj,map_sub,map_neg,map_mul]; simp -- tune
end Ticket
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Ticket.tab_refl
