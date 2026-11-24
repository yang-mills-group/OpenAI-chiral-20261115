import YM.SU5.FiniteGaugeData.Tapestry.Swatch
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

open Pastry
open Reed (Fine think)

variable (S : Finset Cover) (N : Side)

/- Need one more site in `tips S` at every tail in order to extend back to the
period, not just to extend period tests to the cover. A torus edge which has
BOTH ends in `region` lifts to a *true edge with both ends in S*. -/
abbrev Roomy := Hosp (tips S) N
namespace Roomy
variable {S N} (p : Roomy S N)
include p
lemma seats : Hosp S N := ⟨Set.InjOn.mono (fun _ ha=>tips_here _ ha) p.seat_⟩ -- implicit a?
lemma head (a:Cover)(i:Axis)(q:a∈S)(h: wrap (More N) a+step i ∈ region S N): a+step i∈S := by
  obtain ⟨l,u,v⟩:=mem_image.mp h
  have e : l=a+step i:=p.seat_ (tips_here _ u) (tips_there _ q i) (by rw [map_add,wrap_step]; exact v)
  rwa [←e]
end Roomy
lemma tack (p : Roomy S N)(x y : LinksC)(h:Agrees S x y) : Agrees (region S N) (graft S N x) (graft S N y):= by
  rintro ⟨a,i⟩ l t
  obtain ⟨b,w,rfl⟩:=mem_image.mp l
  have ht (U:LinksC) : graft S N U (wrap _ b,i)= U (b,i) := by
    rw [show graft S N _ _ = _ from (onC_spec N (graft S N U) (b,i)).symm]; exact Satin.tail S N (Roomy.seats p) U (b,i) w
  rw [ht x, ht y]; exact h (b,i) w (Roomy.head p b i w t)
lemma untack (p: Hosp S N)(x:Pane N) : Agrees (region S N) (graft S N (onC N x)) x := by
  rintro ⟨a,i⟩ l t
  obtain ⟨b,w,rfl⟩:=mem_image.mp l
  exact (onC_spec N (graft S N (onC N x)) (b,i)).symm.trans ((Satin.tail S N p _ _ w).trans (onC_spec N x (b,i)))
lemma tacked (p : Hosp S N)(x : LinksC) : Agrees S (onC N (graft S N x)) x := fun _ q _=> Satin.tail S N p _ _ q

private lemma nodeIn (a : Cover)(x:Site N)(h:wrap (More N) a=node x):∃ b:Cover, a=nodeC b ∧ wrap N b=x:=by
  let u:=nodeC (Rush.natural x); let k:= periods (More N) a-periods (More N) u
  let b:= Rush.natural x + N.val • k
  have hp:wrap (More N) a=wrap (More N) u:= by unfold u; rw [←node_of,Rush.nat_true]; exact h
  have he : a=u+(More N).val • k:=by
    have e:= carrying (More N) a; have g:=carrying (More N) u
    unfold k; rw [hp] at e; rw [smul_sub]; calc
    _ = (natural ((wrap (More N)) u)+(More N).val • periods (More N) u) + ((More N).val • periods (More N) a - (More N).val • periods (More N) u) := e.symm.trans (by abel)
    _ = _:= by rw [g]
  have hf:a=nodeC b:=by
    rw [he,show (More N).val= (2:ℕ)*N.val from (mul_comm ..),mul_smul]; unfold u b nodeC; rw [smul_add]; abel
  have g:Injective (@node N):= fun x y e=> (assembly N).embed_injective (add_right_cancel (show _+(1:Site (More N))=_+_ from e))
  exact ⟨b,hf,g (by rw [node_of,←hf]; exact h)⟩

section
variable (K:Calibration)(m:Side)
local notation "n"=> (K.c m)
private lemma constCraft {b : Bool} {A : FC (Single (K.c m))} (p : Fine (Tset n) (modesIn n (region S n)) b A) :
    ∃ f:Family K, InTest K true S b f ∧ ∀ x, f m x=A:=by
  induction p with
  | empty=> exact ⟨0,.zero,fun _=>rfl⟩
  | one=> exact ⟨1,.one,fun _=>rfl⟩
  | add _ _ ih iu=> obtain ⟨f,h,w⟩:=ih; obtain ⟨g,k,v⟩:=iu; exact ⟨f+g,.add h k,fun x=>congrArg₂ (·+·) (w x) (v x)⟩
  | grow _ _ ih iu=> obtain ⟨f,h,w⟩:=ih; obtain ⟨g,k,v⟩:=iu; exact ⟨f*g,.mul h k,fun x=>congrArg₂ (·*·) (w x) (v x)⟩
  | scale _ z ih=> obtain ⟨f,h,w⟩:=ih; exact ⟨z • f,.smul z h, fun x=> congrArg (z • ·) (w x)⟩
  | seed i p =>
    obtain ⟨⟨x,i⟩,k⟩:=i
    obtain ⟨a,ha,hb⟩:= Finset.mem_image.mp ((modes_at ..).mp p)
    obtain ⟨y,rfl,h⟩:= nodeIn n a x hb; subst x
    let q:=Lifted.index n y i k
    have hp: q∈Tset n ↔ i∈plusHalf := mem_Tset ..
    let w:= Lifted.winding n y
    have ht:w*w=1:= fee_one _; have he:star w=w:=fee_real _
    by_cases t:i∈plusHalf
    · refine ⟨w • creation K y i k,.smul w (.creator k t ha),fun u=>?_ ⟩; change w • create (w • basisKet q)= _; rw [map_smul,create_put,smul_smul,ht,one_smul]; exact Eq.symm (show (think _).term q = _ from if_pos (hp.2 t))
    refine ⟨(-w) • removal K y i k,.smul (-w) (.remover k t ha),fun u=>?_ ⟩; change (-w) • star (create (w • basisKet q))=_; rw [map_smul,create_put,star_smul,he,smul_smul,neg_mul,ht,neg_one_smul]; exact Eq.symm (show (think _).term q= -takeF q from if_neg (mt hp.mp t))

variable (p: Hosp S (K.c m))
private def pigmentPhase (i:Evens S):ℂ:=(museum S n p i.val).choose
local notation "w" i:max=> pigmentPhase S K m p i
local notation "φ" => star (flake (Tset n)ᶜ)
set_option quotPrecheck false

def eye (i:Evens S) : FC (Single (K.c m)) →ₗ[ℂ] ℂ where
  toFun A:= crumb (twist φ A) (i.val.map (occupy S n p)) / w i
  map_add' a b:= by rw [map_add,crumb_add, add_div]
  map_smul' z a:= by rw [twist_scalar, crumb_scale,mul_div_assoc]; rfl

lemma eye_bounded (i:Evens S)(A) : ‖eye S K m p i A‖ ≤ ‖A‖ := by
  have he:‖(w i)‖=1:=(museum S n p i.val).choose_spec.1
  change ‖(_/ _ :ℂ)‖≤ _; rw [norm_div,he,div_one]
  exact (norm_entry _ _ _).trans_eq (twist_norm ..)
lemma eye_appear (f: Swatch S) (W: Fields n) (i:Evens S): eye S K m p i (appear S K m f W) = daub S (f i) (Prod.map (onC n) (onC n) W) := by
  have he (i:Evens S) : ‖(w i)‖=1 ∧ twist φ (spool n (tagWord S i.val)) = w i • poke (i.val.map (occupy S n p)):=by rw [velvetTag]; exact (museum S n p i.val).choose_spec
  rw [appearSpool, map_sum,sum_eq_single i]; swap
  · intro j _ k; rw [map_smul]; unfold eye; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [(he j).2, crumb_scale,Pastry.chip, if_neg ?_,mul_zero, zero_div, smul_zero]; exact fun e=>k (Subtype.ext (Finset.map_injective (occupy S n p) e.symm))
  swap; · simp
  rw [map_smul]; unfold eye; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [(he i).2,crumb_scale,Pastry.chip,if_pos rfl,mul_one,div_self (by exact norm_pos_iff.mp (zero_lt_one.trans_eq (he i).1.symm)),smul_eq_mul,mul_one]

lemma eye_rep {A : FC (Single (K.c m))} (h: Fine (Tset n) (modesIn n (region S n)) false A):
    A=∑ i:Evens S, eye S K m p i A • spool n (tagWord S i.val):=by
  obtain ⟨g,H,u⟩:= constCraft S K m h
  obtain ⟨f,rfl⟩:= rendered S K H
  rw [←u (1,1), appearRender]; simp_rw [eye_appear]; rw [appearSpool]
lemma eye_readCover (f:Swatch S)(x:PairsC)(i:Evens S): eye S K m p i (appear S K m f (replant S n x))= daub S (f i) x:=by
  rw [eye_appear]; exact (authentic S (f i)).locus _ _ (tacked S n p _) (tacked S n p _)

variable {f: Mark (K.c m)} (r: Roomy S (K.c m))(t: AtSupport false (region S (K.c m)) f)

def mend (r: Roomy S (K.c m))(t: AtSupport false (region S (K.c m)) f): Swatch S := fun i=> pigment S (g:=fun x:PairsC=> eye S K m (Roomy.seats r) i (f (replant S n x))) {
  env := by
    have he:Continuous (eye S K m (Roomy.seats r) i):= LinearMap.continuous_of_finiteDimensional _
    apply Env.along (g:= replant S n) (Girt.pole_w _ _ he t.env) (replant_b S n)
  narrow := fun _=>by contradiction
  locus := fun x y a b=> congrArg _ (t.dep _ _ (tack S n r _ _ a) (tack S n r _ _ b)) }
lemma appear_mend : appear S K m (mend S K m r t)=f:=by
  funext x; rw [appearSpool, eye_rep S K m (Roomy.seats r) (t.allV x)] -- eye_rep rewrites goal f x; beware dependent
  refine sum_congr rfl fun i _=>?_ ; apply congrArg (fun (z: ℂ)=> z • _); unfold mend; rw [daub_pigment]; apply congrArg _ (t.dep _ _ (untack S n (Roomy.seats r) _) (untack S n (Roomy.seats r) _))
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.appear_mend
