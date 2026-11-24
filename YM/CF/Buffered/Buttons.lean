import YM.CF.Buffered.Solvency
/-!
# Identify actual mark as a rectangular label on top. We allow labels varying
on tile boundaries like `Logo`; however the given marks have all their input
feet in the interior, no dependence on knobs in the Servo.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 510000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Gloss Scroll Push.SectorMeasure Ordered Cin Stripe Tile
open Reflect Window Tulip Skye Rush Lifted Heat Solid Burn Ballad Advance
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Wings
variable {m v p B l q:Side}{e:ℕ}
local notation "N" => CSide m B
local notation "S" => Domain v B
local notation "W" => Post (CSide v B)
local notation "V" => GridM v B
local notation "Λ" => Spin
local notation "X" => Single N
local notation "δ" => Uniform p
variable (A:Ordered m v p)(r:Rail (Uniform p))
local notation "G" => A.sugar B
local notation "H" => A.spirit B
-- stay in original mark basis for orientation. insertTop uses submatrix algebra crossL Helix.
def regionX (B:Side) := (Ordered.erect A B).trans (helix (CSide m B)).symm
local notation "Q" => regionX A B
local notation "g" => point (regionX A B) r
local notation "Ṗ" => point (Ordered.erect A B) r
abbrev liftZ {n d b:Side}(K:Planck n d b)(r:Rail (Uniform b))(z:Post d) := K.sail r+z.val
lemma held (x:W)(j:SpinIdx)(s:SU.Slot): g (Bays.install Spin x (j,s))=Lifted.index N (liftZ (A.spirit B) r x) j s:=rfl
lemma natural_true {n d b:Side}(K:Planck n d b)(r:Rail (Uniform b))(x:Post d) : natural (K.zone r x.val)=liftZ K r x:=by
 funext i; unfold natural; rw [K.pilot r x]; simp only [liftZ, Planck.sail,Pi.add_apply,Nat.cast_add,Nat.cast_mul,Int.toNat_of_nonneg (x.nonneg i)]
lemma toll_one {n:Side}(x:Site n) : winding n (natural x)=1:=by
 have he:= carrying n (natural x); rw [Rush.nat_true] at he
 unfold Lifted.winding; rw [show periods n (natural x)=0 from ?_]; · simp [fee]
 apply nsmul_right_injective (M:=Cover) n.property.ne'; change n.val • _=n.val • (0:Cover); rw [nsmul_zero]; exact add_left_cancel (show natural x+n.val • periods n (natural x)=natural x+0 from he.trans (add_zero _).symm)
lemma basis_raw (x:W)(j:SpinIdx)(s:SU.Slot): basisC N (liftZ (A.spirit B) r x) j s=basisKet (g (Bays.install Spin x (j,s))):=by rw [held, basisC,← natural_true H r x,toll_one,one_smul]
lemma shorter_up (i:Axis) : upstairs' S r i=2*upstairs' (CSide v B) r i:=by simp [upstairs']; ring
lemma flee_next (i:Axis) (g':¬endsAt r i) (x:W) : (plane i (upstairs' S r i)).flee (liftZ H r x)= liftZ H (Region.next i r) (shades {i} x) :=by
 unfold liftZ; rw [Solid.spill H r i rfl g']; funext j; simp only [flee_pos,Pi.add_apply,Pi.smul_apply,step_apply]; by_cases h:i=j; · subst j; rw [shorter_up]; simp [Planck.sail,upstairs',Roost.shades_eq _ (mem_singleton_self _),wall_mem i (mem_univ _)]; ring
 simp only [h, Ne.symm h, if_false, Roost.shades_other x (mem_singleton.not.mpr (Ne.symm h)), smul_zero, add_zero]
lemma stitched (i:Axis)(p:¬endsAt r i) : Framed (point (regionX A B) r) (point (regionX A B) (Region.next i r)) (carR i (upstairs' S r i) N) (turnF i v B):=by
 intro y; obtain ⟨⟨z,j,s⟩,rfl⟩:= (Bays.wall W Spin).surjective y
 let t:= Region.next i r; let A':=plane i (upstairs' S r i); let f:=point Q t; let q':= Bays.install Spin (shades {i} z)
 change acts _ (basisKet (g (Bays.install Spin z (j,s))))=coat f (acts _ (basisKet (Bays.install Spin z (j,s))))
 rw [←basis_raw, acted_basisC, flee_next A r i p, show acts _ (basisKet (Bays.install Spin z (j,s)))=_ from seat_mate i z (j,s)]; have he : acts (mirrorSpin i).val (basisKet  (j,s))=∑ k,pin i k j • basisKet (k,s):=by
    apply PiLp.ext; rintro ⟨b,y⟩; simp_rw [basis_act,WithLp.ofLp_sum,Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,basis_apply]; by_cases h:s=y; · subst y; simp [mirrorSpin, eq_comm]
    simp [mirrorSpin,h, Ne.symm h]; -- tune
 rw [he]; simp_rw [map_sum,map_smul, basis_shell]; exact sum_congr rfl fun k _=>congrArg _ (basis_raw A t (shades {i} z) k s)
lemma ferry_wire (B:Side)(i:Axis)(p:¬endsAt r i): through B (A.ferry r (Region.next i r) {i})= fling i (upstairs' (Domain v B) r i) (CSide m B):=by
 funext f; unfold Trip.through; rw [ferry_gauge, fling_eq]; change pull (glazed (maskC {i})) _ _=_; rw [mirror_mask]; congr 2
 -- use sail formula and mirror component
 funext j; rw [Solid.spill (A.sugar B) r i rfl p]; by_cases h:i=j <;> simp [Signed.mirror,Signed.act,h,Ne.symm, upstairs', Planck.sail, lengthV]; rw [h]; ring
include A in
lemma sign_shade (i:Axis)(b: Badge v B): b.reflected (Region.next i r) = (b.reflected r).reflect i:=by
 have ht:= shade_next r i A.onGrid i; simp only [ite_true] at ht; let t:= Region.next i r; unfold Badge.reflected
 have he(j:Axis)(p:j≠i): j∈shade t ↔ j∈shade r:=by rw [show t=Region.next i r from rfl,shade_next r i A.onGrid,if_neg p]
 by_cases h:i∈shade r
 · have p:i∉shade t:=fun u=>ht.1 u h; have hx:shade r=insert i (shade t):=by ext j; by_cases v:j=i; subst j; simp [h]; rw [mem_insert, or_iff_right v,he j v]
   rw [hx, Badge.stencil_at _ b p, Badge.back]; -- tune
 have hx:shade t=insert i (shade r):=by ext j; by_cases v:j=i; subst j; simp [t, ht.2 h]; rw [mem_insert, or_iff_right v, he j v]
 rw [show shade (Region.next i r)=_ from hx, Badge.stencil_at _ b h]
-- represents all inputs (not just secure interior). Orientation pays y→ferry
-- using actual shared field transformation. Badge used only at same V.
def stamps (r: Rail (Uniform p))(z: Mark (CSide m B))(Z:Badge v B):Prop:= ∀ x: Pack m B, both z x.1=into (point (regionX A B) r) (Z.label (reel r (A.fromCube x)))
lemma stamps_ref {z: Mark N}{Z: Badge v B}(h:stamps A r z Z) (i:Axis)(g':¬endsAt r i): stamps A (Region.next i r) (reflMark i (upstairs' S r i) z) (Z.reflect i):=by
 intro x; let t:=onPack B (A.ferry r (Region.next i r) {i}) x; let s:=upstairs' S r i; change theta (carR i s N) (both z (fling _ _ _ x.1))= _; rw [show fling i s N x.1=t.1 from (congr_fun (ferry_wire A r B i g') x.1).symm, h t,(stitched A r i g').theta _ (Z.state _),show reel r (A.fromCube t)=_ from ferry_extract ..]; rfl
lemma interior (p:0<e) {x y:Pack m B} (h:(reel r (A.fromCube x)).1=(reel r (A.fromCube y)).1): Agrees (wallZ (A.sugar B) r e) x.1 y.1:= by
 let G':= A.sugar B; rintro ⟨u,i⟩ hu _; change x.1 (u,i)= y.1 (u,i); obtain ⟨z,b,rfl⟩:=(Solid.seam _ r e u).1 hu; -- tune
 let q: Roost S {i}:=⟨z,fun j=>by specialize b j; unfold topwall; split <;> omega⟩
 exact (A.butter x r i q).symm.trans ((congrFun (congrFun h i) q).trans (A.butter y r i q))
lemma mode_to (p:0<e): modesIn N (wallZ (A.sugar B) r e) ⊆ lows g :=by
 intro i he; obtain ⟨⟨t,x,u⟩,f⟩:= (regionX A B).surjective i -- Spin inference bad
 subst i; change point (regionX A B) t ((Bays.install Spin x) u) ∈ lows g -- tactic goal shape
 rw [modes_at] at he; change node ((A.spirit B).zone t x.val) ∈ _ at he; rw [up_sends (K:=A)] at he; have hv:= Solid.keep (A.sugar B) r p _ he
 apply Finset.mem_map.mpr; refine ⟨_,mem_univ (Bays.install Spin x u),?_⟩; rw [← show t=r from ?_]
 let K':= A.sugar B; let Y_: Post (Domain v B):=Ordered.upstairs v B x
 have hp : K'.zone t Y_.val=Crust.Grid.send K' (t,wrap (Domain v B) Y_.val):=by rw [Crust.Grid.toe]; refine congrArg (fun x=> K'.zone t x) (funext fun j=>?_); unfold natural; rw [wrap_here,int_val _ (Y_.nonneg j) (Y_.below j (mem_univ _)),Int.toNat_of_nonneg (Y_.nonneg j)]
 rw [←hv]; rw [show (A.sugar B).zone t _=Crust.Grid.send K' (t,wrap (Domain v B) Y_.val) from hp]; exact (Crust.Grid.lesser_here ..).1.symm
lemma dye {z:Mark (CSide m B)}(b:0<e)(H': AtSupport false (wallZ G 0 e) z) : ∃ Z:Badge v B, stamps A 0 z Z ∧ ∀ x y: Locale v B, x.1=y.1 → Z.label x=Z.label y:=by
 let K:=point Q (0: Rail δ); let f:=into K; obtain ⟨l,Y⟩:= LinearMap.exists_leftInverse_of_injective f.toLinearMap (LinearMap.ker_eq_bot_of_injective (show Function.Injective f from Cin.into_inj K))
 let a(x:Locale v B) := both z (whole A x).1; let m(x:Locale v B):=l (a x)
 have hv(F:FC V): l (f F)=F:=LinearMap.congr_fun Y F; have ht(x:Locale v B): ∃ B: FC V, Sector univ false B ∧ f B=a x:= Cin.preimage K (Window.fine_enlarge (mode_to A 0 b) (H'.allV ((whole A x).1,(whole A x).1))).sector
 refine ⟨⟨m,Girt.pole_w a l l.continuous_of_finiteDimensional (Env.along («g»:=fun x:Locale v B=>((whole A x).1,(whole A x).1)) H'.env (((continuous_fst.comp (whole_cont A)).measurable).prodMk ((continuous_fst.comp (whole_cont A)).measurable))),fun x=>?_⟩,fun v=>?_,fun x y hp =>?_⟩
 · obtain ⟨v,p,h⟩:=ht x; unfold m; rw [←h,hv]; exact p
 · let R:= reel 0 (A.fromCube v); obtain ⟨x,p,h⟩:= ht R; change _=f (l (a R)); have he:= interior A 0 b (show (reel 0 (A.fromCube v)).1=(reel 0 (A.fromCube (whole A R))).1 from congrArg Prod.fst (whole_zero ..).symm); rw [←h,hv,h]; exact H'.dep _ _ he he
 · apply congrArg l; have he:=interior A 0 b (show (reel 0 (A.fromCube (whole A x))).1=(reel 0 (A.fromCube (whole A y))).1 by rw [whole_zero,whole_zero,hp]); exact H'.dep _ _ he he
lemma flashed {z: FC (GridM v B)} {b:Bool} (p: Sector univ b z) : crossL (helix (CSide m B)).symm (into g z)=into Ṗ z :=by
 induction p with
 | zero=>rw [map_zero,map_zero,cross_zero]
 | one=>rw [map_one,map_one,cross_one]
 | up i _=>rw [put_in, put_in]; exact (cx_p ..).1
 | down i _=>rw [take_in,take_in]; exact (cx_p ..).2
 | mul _ _ p q=>rw [map_mul,map_mul,cx_m,p,q]
 | add _ _ p q=>rw [map_add,map_add,cross_add,p,q]
 | scale _ c p=>rw [map_smul,map_smul,cross_scalar,p]
lemma identifies {z:Mark (CSide m B)}{Z:Badge v B}(h:stamps A r z Z)(x:Pack m B) : insertTop (both z) x=into Ṗ (Z.label (reel r (A.fromCube x))) := by unfold insertTop; rw [h x]; exact flashed A r (Z.state _)
end Wings
namespace Ticket
open Wings
variable {e x:ℝ} {m p B v:Side} (K:Ticket m v B p e x) (Z:Badge v B) (q:Clip)(β u:ℝ)
lemma self_log {z: Mark (CSide m B)}(h:stamps K.K 0 z Z) : singleZ K Z q β u= heatNum K.pin K.W q β x e u (Brace.northZ m B) (insertTop (both z)):=by rw [singleZ]; apply congrArg; exact funext fun i=> (identifies K.K 0 h i).symm
lemma insert_prop (F:Mark (CSide m B))(D:Mark (CSide m B)): insertTop (both (D*F))=insertTop (both D)*insertTop (both F):=funext fun _=> cx_m ..
variable (h:Rail (Uniform p)→ Mark (CSide m B)) (L: List (Rail (Uniform p)))
lemma coat_y (k:L.toFinset=univ)(z:L.Nodup)(v':∀ i, stamps K.K i (h i) (Z.reflected i)) : K.moment Z q β u=heatNum K.pin K.W q β x e u (Brace.northZ m B) (insertTop (both ((L.map h).prod))):=by
 unfold moment; apply congrArg; funext i; unfold Ticket.estate Rect.logo; let Q(x:Rail (Uniform p)):= reel x (K.K.fromCube i); let Y:=Ordered.erect K.K B; let f:=Rect.Badge.one Y (Z.reflected) Q; rw [show Rect.Badge.affix _ _ _= (L.map f).prod from pal_list _ (Rect.Badge.paired ..) _ L k z]
 suffices hv:∀ M:List (Rail (Uniform p)),(M.map f).prod=insertTop (both (M.map h).prod) i from hv L
 intro M; induction M with
 | nil=> exact (cross_one _).symm
 | cons i l ih=> simp only [List.map_cons,List.prod_cons,insert_prop, Pi.mul_apply]; rw [ih]; exact congrArg (fun x=> x*_) ((identifies _ i (v' i) _).symm) -- tune collision i
end Ticket
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Wings.dye
#print axioms YM.CF.Buffered.Region.Wings.stamps_ref
#print axioms YM.CF.Buffered.Region.Ticket.coat_y
