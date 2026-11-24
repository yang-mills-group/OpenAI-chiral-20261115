import YM.SU5.FiniteGaugeData.Tower.Control
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# The cover test class is complete for EVEN finite-lattice chiral marks at
fixed support as soon as that support geometrically embeds including edge
incidence (all tt-bounded Borel functions on the two field inputs).
Identify the testing arguments of the limit with native periodic marks with
only `AtSupport` there. Coarse reading never moved to a different Loom.
`Tivoli` gives an all-data embedding threshold of this statement; the size
condition differs from Hosp precisely due to edge support (also need to
preserve positive-edge *incidence*). We use:
* flake coefficient extraction by crumbs as in Hearth
* Fine sufficiency by induction at fixed pair value; measurable coefficients
are then obtained by cutting a fixed read-off of those crumbs, **not** by
measurable selection of that Fine expression
* uniqueness even after moving overlap, by box_ext
-/
open Reed (Fine think)
open Fock Pastry Tenant
section patches
variable (S:Finset Cover)(n:Side)
structure Tivoli :Prop where
 tips_x: Hosp (Satin.tips S) n
lemma Tivoli.hosp (p:Tivoli S n): Hosp S n:=⟨p.tips_x.seat_.mono fun _ h=> tips_here S h⟩
lemma wrap_nodes (x:Site n)(a:Cover) (p:wrap (More n) a=node x):∃ b:Cover,a=nodeC b∧ wrap n b=x:=by
 rw [← wrap_lift x, node_of] at p
 have ht(i:Axis): ((More n).val:ℤ) ∣ nodeC (Lattice.lift x) i-a i := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congrFun p i)
 choose w g using ht
 let b:Cover:=fun i=> Lattice.lift x i - (n.val:ℤ)*w i
 have e:a=nodeC b:=by
    ext i; unfold nodeC; simp only [two_smul,Pi.add_apply,Pi.one_apply]
    specialize g i; unfold nodeC at g; simp only [two_smul,Pi.add_apply,Pi.one_apply,show (More n).val=n.val*(2:ℕ) from rfl,Nat.cast_mul,Nat.cast_ofNat] at g; unfold b; linarith
 rw [←node_of,wrap_lift] at p; exact ⟨b,e,needle (by rw [node_of,←e]; exact p)⟩
lemma all_seats {t: Single n} (h:t∈modesIn n (Satin.region S n)):∃ u: Satin.Tag S,Lifted.index n (who S u).1 (who S u).2.1 (who S u).2.2=t:=by
 obtain ⟨⟨x,i⟩,b⟩:= t; rw [modes_at] at h; obtain ⟨q,v,p⟩:= mem_image.mp h
 obtain ⟨z,rfl,hq⟩:=wrap_nodes n x q p
 let c:Satin.Tag S:=⟨(z,i,b),v⟩; exact ⟨c,show ((wrap n z,i),b)= _ by rw [hq]⟩
lemma graft_cont (n:Side):Continuous (graft S n):=by apply continuous_pi; intro a; unfold Satin.graft; split; exact continuous_apply _; exact continuous_const
lemma replant_cont: Continuous (replant S n):= ((graft_cont S n).comp continuous_fst).prodMk ((graft_cont S n).comp continuous_snd)
section
variable (p:Tivoli S n)
include p
lemma based (v v':LinksC)(h:Agrees S v v'): Agrees (Satin.region S n) (graft S n v) (graft S n v'):=by
 rintro ⟨x,i⟩ t u; obtain ⟨a,r,rfl⟩:=mem_image.mp t; obtain ⟨b,g,w⟩:=mem_image.mp u
 have he:a+step i=b:= p.tips_x.seat_ (tips_there S r i) (tips_here S g) (by rw [map_add,wrap_step]; exact w.symm)
 have hx(V:LinksC):graft S n V (wrap (More n) a,i)=V (a,i):= (onC_spec n (graft S n V) (a,i)).symm.trans (tail S n p.hosp V _ r)
 rw [hx,hx]; exact h (a,i) r (he.symm ▸ g)
lemma graft_native (v:Pane n): Agrees (Satin.region S n) (graft S n (onC n v)) v:=by
 rintro ⟨x,i⟩ t u; obtain ⟨a,r,rfl⟩:=mem_image.mp t
 have hx(V:LinksC):graft S n V (wrap (More n) a,i)=V (a,i):= (onC_spec n (graft S n V) (a,i)).symm.trans (tail S n p.hosp V _ r)
 rw [hx]; exact onC_spec n v (a,i)
end
end patches

section extend
variable (S:Finset Cover)(K':Calibration)(n:Side)
local notation "s₀"=> K'.c n
local notation "l₀"=> Satin.region S (K'.c n)

-- at any frozen pair point, realize the operator by a mark in the grammar
-- val all constant on all periods; here used just at n. odd realization too.
lemma realizes_modes {b:Bool}{A:FC (Single s₀)}(h:Fine (Tset s₀) (modesIn s₀ l₀) b A):∃ f:Family K',InTest K' true S b f∧ ∀ x,f n x=A:=by
 induction h with
 | empty=> exact ⟨0,.zero,fun _=> rfl⟩
 | one=> exact ⟨1,.one,fun _=>rfl⟩
 | grow _ _ x t=> obtain ⟨i,a,b⟩:=x; obtain ⟨j,v,w⟩:=t; exact ⟨i*j,.mul a v,fun h=>congrArg₂ (HMul.hMul (γ:=FC _)) (b h) (w h)⟩
 | add _ _ x t=> obtain ⟨i,a,b⟩:=x; obtain ⟨j,v,w⟩:=t; exact ⟨i+j,.add a v,fun h=>congrArg₂ (HAdd.hAdd (γ:=FC _)) (b h) (w h)⟩
 | scale _ c x=> obtain ⟨i,a,b⟩:=x; exact ⟨c • i,.smul c a,fun x=>congrArg (fun t:FC _=>c • t) (b x)⟩
 | seed i t=>
    obtain ⟨u,e⟩:= all_seats S _ t; obtain ⟨⟨x,j,b⟩,g⟩:=u
    change Lifted.index s₀ x j b=i at e
    subst i; let d:= Lifted.winding s₀ x; have hd: d≠0:= norm_pos_iff.mp ((Rush.fee_norm _).symm ▸ zero_lt_one) -- check
    let k := Lifted.index s₀ x j b
    by_cases hi: j∈plusHalf
    · refine ⟨d⁻¹ • creation K' x j b,.smul _ (.creator b hi g),fun r=>?_⟩
      change d⁻¹ • create (basisC _ _ _ _) = (if k∈ Tset s₀ then _ else _)
      rw [if_pos (show k ∈ Tset _ from (mem_Tset ..).mpr hi),basisC,map_smul,create_put]; rw [smul_smul,inv_mul_cancel₀ hd,one_smul]
    refine ⟨-d⁻¹ • removal K' x j b,.smul _ (.remover b hi g),fun r=>?_⟩
    change -d⁻¹ • Fock.remove (basisC ..)= (if k∈Tset s₀ then _ else _)
    rw [if_neg (show k∉Tset _ from fun h=>hi ((mem_Tset ..).1 h)),basisC,Fock.remove,map_smul,star_smul,create_put]
    change -d⁻¹ • (star d • takeF k)= -takeF k
    rw [show star d=d from Rush.fee_real _,smul_smul,neg_mul,inv_mul_cancel₀ hd,neg_one_smul]

variable (t:Tivoli S (K'.c n))
local notation "φ"=> star (flake (Tset (K'.c n))ᶜ)
local notation "J"=> occupy S (K'.c n) (t.hosp)
noncomputable def sigil (t:Tivoli S (K'.c n))(q:Evens S):ℂ:= (museum S (K'.c n) t.hosp q.val).choose
local notation "σ"=> sigil S K' n t
lemma sigil_unit (q:Evens S): ‖σ q‖=1:= (museum S (K'.c n) t.hosp q.val).choose_spec.1
lemma sigil_ne (q:Evens S): σ q≠0:= norm_pos_iff.mp ((sigil_unit S K' n t q).symm ▸ zero_lt_one)
lemma sigil_expands (q:Evens S): twist φ ((velvet S (K'.c n)).tag q.val)= σ q • poke (q.val.map J):= (museum S (K'.c n) _ q.val).choose_spec.2

def costume(A:FC (Single (K'.c n))) (q:Evens S):= (σ q)⁻¹ * crumb (twist φ A) (q.val.map J)
local notation "sliceA"=> costume S K' n t
lemma biotech (A:FC (Single (K'.c n)))(q:Evens S):‖sliceA A q‖≤‖A‖:= by unfold costume; rw [norm_mul,norm_inv,sigil_unit,inv_one,one_mul]; exact (norm_entry ..).trans_eq (twist_norm ..)
lemma linearity{q:Evens S}(x y:FC (Single (K'.c n)))(z:ℂ):sliceA (z • x+y) q=z*sliceA x q+sliceA y q:=by unfold costume; rw [map_add,twist_scalar,Pastry.crumb_add,Pastry.crumb_scale]; ring
lemma splice{q:Evens S}:Continuous (fun A=>costume S K' n t A q):=by
 unfold costume Pastry.crumb; apply Continuous.mul continuous_const; exact (breeze _).matrix_elem _ _
variable {f : Family K'}
lemma evaluated (a:Evens S→Purse S)(h:f=∑ q:Evens S,note K' (a q).val (tagWord S q.val))(x:Fields (K'.c n)): twist φ (f n x)=∑ q:Evens S,(a q).1 (Prod.map (onC _) (onC _) x) • (σ q • poke (q.val.map J)):=by
 rw [h]; simp_rw [Finset.sum_apply,map_sum,note_v,spool_sing,velvetTag,twist_scalar]; exact Finset.sum_congr rfl fun q _=> congrArg ((a q).val (Prod.map (onC _) (onC _) x) • ·) (sigil_expands S K' n t q)
lemma recovered (a:Evens S→Purse S)(h:f=∑ q:Evens S,note K' (a q).val (tagWord S q.val))(x:Fields (K'.c n))(q:Evens S): sliceA (f n x) q=(a q).val (Prod.map (onC _) (onC _) x):=by
 unfold costume
 rw [evaluated S K' n t a h x,crumb_sum,sum_eq_single q,crumb_scale,crumb_scale,Pastry.chip,if_pos rfl,mul_one,mul_left_comm,inv_mul_cancel₀ (sigil_ne S K' n t q),mul_one]
 · intro j _ K0; rw [crumb_scale,crumb_scale,Pastry.chip,if_neg ?_,mul_zero,mul_zero]; exact fun x=> K0 (Subtype.ext (Finset.map_injective J x.symm))
 simp
lemma stitched {A:FC (Single (K'.c n))}(p: Fine (Tset s₀) (modesIn s₀ l₀) false A): A=∑ q:Evens S,sliceA A q • (velvet S (K'.c n)).tag q.val:=by
 obtain ⟨f,h,e⟩:= realizes_modes S K' n p; obtain ⟨a,v⟩:= circulation S K' h
 let x:Fields (K'.c n):=(1,1)
 rw [←e x]; trans (∑ q:Evens S,note K' (a q).val (tagWord S q.val)) n x
 · rw [←v]
 simp_rw [Finset.sum_apply,note_v,spool_sing,velvetTag,recovered S K' n t a v x]

-- measurable Borel lifting of coefficients
variable (fP:Mark (K'.c n)) (h:AtSupport false (Satin.region S (K'.c n)) fP)
abbrev piece (q:Evens S)(x:PairsC):ℂ:= sliceA (fP (replant S (K'.c n) x)) q
include h
lemma painting (q:Evens S):Coeff true S (piece S K' n t fP q):=by
 refine ⟨fun _=>by contradiction,Girt.pole_w (fun v:PairsC=>fP (replant S (K'.c n) v)) (fun x=>costume S K' n t x q) (splice S K' n t) (Env.along (g:=replant S (K'.c n)) h.env (replant_b S _)),?_⟩
 intro x y a b; exact congrArg (fun z=>costume S K' n t z q) (h.dep _ _ (based S _ t _ _ a) (based S _ t _ _ b)) -- tune `..`
omit h
noncomputable def extendAtlas:Family K':=∑ q:Evens S,note K' (piece S K' n t fP q) (tagWord S q.val)
local notation "Ξ"=>extendAtlas S K' n t fP
include h
lemma dictionary: InTest K' true S false Ξ:=by
 refine .sum _ _ fun (q:Evens S) _=>?_
 have ht:=Sound.note_t K' _ (painting S K' n t fP h q) (brand S q.val); rw [q.property] at ht; exact ht
lemma native: Ξ n=fP:=by
 funext x
 have hr: fP (replant S (K'.c n) (Prod.map (onC _) (onC _) x))= fP x:= h.dep _ _ (graft_native S _ t _) (graft_native S _ t _)
 unfold extendAtlas; simp_rw [Finset.sum_apply,note_v,piece,spool_sing,velvetTag,hr]; exact (Tower.stitched S K' n t (h.allV x)).symm
-- also check continuous FIRST-link case. narrow transfer need not be expected;
-- just check cover language for matching the determining physical probes.
variable (F : Evaluation (K'.c n))(F':fP=toMark F)
include F'
lemma narrow_dict (v:Continuous F):InTest K' false S false Ξ:=by
 have ht(q):= painting S K' n t fP h q
 have hp(q):Coeff false S (piece S K' n t fP q):=⟨fun _=>⟨fun x=>costume S K' n t (F (graft S (K'.c n) x)) q,(splice S K' n t).comp (v.comp (graft_cont S _)),F'.symm ▸ rfl⟩,(ht q).2,(ht q).3⟩
 refine .sum _ _ fun (q:Evens S) _=>?_
 have ht:=note_t K' _ (hp q) (brand S q.val); rw [q.property] at ht; exact ht
end extend

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.native
