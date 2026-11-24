import YM.CF.BPress.Wealth.Terms
/-! Plaquette slot read in any oriented channel, with same sign/permutation of background and perturbations. Eq:B-direct uses curl x+shift from linearizing link perturbations. Treat all four actual links explicitly. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix
open SU Push.Local
variable {s:Side}{G:Gauge}(v:Signed)

def address (i : Link s) := ((posDir i.2).rotate v).used (v.act i.1) -- native physical coordinate
lemma address_inv (i :Link s) : address v i= if v.flip i.2 then (v.act i.1-step (v.perm i.2), v.perm i.2) else (v.act i.1,v.perm i.2):=by simp only [address, Step.rotate, Step.used,posDir,Bool.false_xor]
lemma act_step (i : Site s)(a:Axis): v.act (i+step a)= v.act i + (if v.flip a then -(step (v.perm a) : Site s) else step (v.perm a)):=by rw [v.act_add]; exact congrArg _ (by rw [←Step.vec_pos,←Step.vec_rotate]; simp only [Step.rotate, posDir,Step.vec, Bool.false_xor])
lemma photo_edge (S:Support s)(i:Link s)(t:i∈inside S): address v i∈ inside (photo v S):=by
 rw [inside_iff,address_inv]; let g(k:Site s)(p:k∈S): v.act k∈ photo v S:= by
   have h:v.act k= turnSites v 0 k:=by simp [turnSites,Signed.actEquiv]
   rw [h]; exact mem_image_of_mem _ p; -- tune scope
 obtain ⟨p,q⟩:= inside_iff ..|>.mp t; have ht:=g _ q; rw [act_step] at ht; split; next h=> rw [if_pos h,←sub_eq_add_neg] at ht; exact ⟨ht,by simpa using g _ p⟩
 next h=> exact ⟨ g _ p, by rwa [if_neg h] at ht⟩
-- apply sign (-1) with transported orientation price
lemma orient_read (i:Link s)(U:Config G s): pull v 0 U i= if v.flip i.2 then (U (address v i))⁻¹ else U (address v i):=by simp only [pull,Step.read, Step.rotate, affine,add_zero,posDir,address,Bool.false_xor]
lemma pull_close (i : Link s)(U V:Config G s) : chord (pull v 0 U i) (pull v 0 V i)=chord (U (address v i)) (V (address v i)):=by rw [orient_read,orient_read]; split; simp; rfl
lemma addr_id (i : Link s): address 1 i=i:=by simp [address_inv]
lemma addr_axis (i:Link s): (address v i).2=v.perm i.2:=by rw [address_inv]; split <;> rfl

def opSigns {X:Type*}[Neg X] (v:Signed)(i:Axis)(x:X) := if v.flip i then -x else x
def orbitW (v:Signed)(w:Directions G s)(i:Link s) := opSigns v i.2 (w (address v i))
def brandW (w:Directions group s)(q:Bonding s)(k:Fin 4):= orbitW v w (aperture q k)
lemma orbit_meas (i:Link s): Continuous fun w: Directions G s=> orbitW v w i:=by unfold orbitW opSigns; split <;> fun_prop
lemma orbit_fee (i:Link s)(w:Directions G s): ‖orbitW v w i‖= ‖w (address v i)‖:=by unfold orbitW opSigns; split; simp; rfl
@[simp] lemma orbit_id (i:Link s)(w:Directions G s): orbitW 1 w i=w i:=by simp [orbitW,opSigns,addr_id]
def turnout (v : Signed) : Directions G s →ₗ[ℝ] Directions G s where
 toFun := orbitW v
 map_add' x y:=by funext i; unfold orbitW opSigns; split <;> simp_all [add_comm]
 map_smul' c x:=by funext i; unfold orbitW opSigns; split <;> simp_all

def oriDir (k : Axis):= opSigns v k (backgroundDir (v.perm k))
@[simp] lemma dirId (k:Axis): oriDir 1 k=backgroundDir k:=by simp [oriDir,opSigns]
def rollA (i:Axis)(a : ℝ):= group.lieExp (a • oriDir v i)
def review (i : Axis)(a : ℝ)(w:group.Color) := if v.flip i then group.lieExp w*rollA v i a else rollA v i a*group.lieExp w
lemma bg_rotate (i : Link s)(y : ℝ): pull v 0 (background y) i= rollA v i.2 (aA y):=by
 rw [orient_read]; unfold background rollA oriDir opSigns; rw [addr_axis]; split; simp [chord.exp_neg]; rfl
lemma review_bg (i:Axis)(a : ℝ): review v i a 0=rollA v i a:=by unfold review; split<;> simp
lemma review_eq (i:Link s)(y:ℝ)(w:Directions group s): pull v 0 (actuated y w) i= review v i.2 (aA y) (orbitW v w i):=by
 rw [orient_read]; unfold actuated review orbitW rollA oriDir opSigns; unfold background; rw [addr_axis]; split; simp [chord.exp_neg]; rfl
/-- color sum (linear) in positive square (read in each channel). -/
def circle (w:Fin 4→G.Color) := w 0+w 1-w 2-w 3
def orbitP (v:Signed)(t:Bonding s) : Directions group s→ₗ[ℝ] group.Color where
 toFun w:= circle (brandW v w t)
 map_add' w x:=by simp only [brandW,circle,show orbitW v (w+x)=_ from (turnout v).map_add w x,Pi.add_apply]; change _= _; simp only [turnout,LinearMap.coe_mk, AddHom.coe_mk]; abel
 map_smul' c w:=by simp only [brandW,circle,show orbitW v (c • w)=_ from (turnout v).map_smul c w,Pi.smul_apply, RingHom.id_apply,smul_sub,smul_add]; rfl
lemma orbitP_id (t:Bonding s)(w:Directions group s): orbitP 1 t w= circle (fun i=> w (aperture t i)):=by rw [show orbitP 1 t w=_ from rfl]; apply congrArg circle; exact funext fun i=> orbit_id .. -- tune
def psi (p:PlaqAxes):= group.ad (oriDir v p.val.1) (oriDir v p.val.2)

def readA {X:Type*}[Group X] (a:Fin 4→ X) := a 0*a 1*(a 2)⁻¹*(a 3)⁻¹
lemma readA_val (U: Config group s)(x:Bonding s): faceValue U x=readA (fun i=> U (aperture x i)):= Travel.price ..
def colorDir (p:PlaqAxes)(i:Fin 4) := ![p.val.1,p.val.2,p.val.1,p.val.2] i
lemma dir_ap (p:Bonding s)(i:Fin 4): colorDir p.2 i=(aperture p i).2:=by fin_cases i <;> rfl

def panel (p:PlaqAxes)(z : ℝ)(x:Fin 4→group.Color):= readA fun i=> review v (colorDir p i) z (x i)
lemma rolled (y:ℝ)(w:Directions group s)(x: Bonding s): faceValue (pull v 0 (actuated y w)) x= panel v x.2 (aA y) (brandW v w x):=by
 rw [readA_val]; apply congrArg readA; funext i; rw [review_eq,dir_ap]; rfl
lemma color_panel (y:ℝ)(x:Bonding s): faceValue (pull v 0 (background y)) x=panel v x.2 (aA y) 0:=by
 rw [readA_val]; unfold panel; apply congrArg readA; funext i; rw [bg_rotate,dir_ap,Pi.zero_apply, review_bg]
lemma panel_bg (p:PlaqAxes)(x:ℝ): panel v p x 0=chord.panel (oriDir v p.val.1) (oriDir v p.val.2) x:=by
 unfold panel readA; simp_rw [Pi.zero_apply,review_bg]; rfl
lemma reader_cost (a b:Fin 4→G.El){x:ℝ}(p:∀ i,chord (a i) (b i)≤x): chord (readA a) (readA b)≤4*x:=by
 unfold readA; apply (chord.product ..).trans; apply le_trans (add_le_add (chord.product ..) le_rfl); apply le_trans (add_le_add (add_le_add (chord.product ..) le_rfl) le_rfl); rw [chord.inv,chord.inv]; linarith only [p 0,p 1,p 2,p 3]
end YM.CF.BPress.Wealth
