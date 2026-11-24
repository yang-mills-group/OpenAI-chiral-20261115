import YM.CF.BProof.Mote.Hymn
import YM.CF.Bloom.Flux
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive Tap Haro
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
set_option synthInstance.maxSize 28000
namespace Leg
variable {m n : Type}[LinearOrder m][Fintype m][LinearOrder n][Fintype n]
variable {N P:Side}(G:Ratio N P)(j:ℕ) (Q:SpaceM)(M:Male)
open TripD
abbrev Snow (W:Support (More N))(b:Bool): FC (Single N)→ Prop:=Reed.Fine (Tset _) (modes W) b
def winter (W:Support (More N))(b:Bool):Submodule ℂ (FC (Single N)) where
 carrier:=Snow W b
 zero_mem':=Reed.Fine.empty _
 add_mem':= Reed.Fine.add
 smul_mem':= fun z _ p=> Reed.Fine.scale p z
variable {W:Support (More N)}{A A':FC (Single N)}{b:Bool}
open Reed (Fine)
lemma reach_e {T:Finset m}{x:Ket m}(p:acts (cutM T) x=0){i:m}(v:i∈T):x.ofLp i=0:=by rw [← show (acts (cutM T) x).ofLp i=x.ofLp i from (cut_apply ..).trans (if_pos v),p]; rfl
lemma put_here {X Y:Finset m}{x:Ket m} (p:acts (cutM X) x=x)(h:acts (cutM Y) x=x): Fine X Y true (create x):=by
 rw [create_def]; refine Fine.sumF _ _ ?_; intro i _; by_cases hx:x.ofLp i=0; rw [hx,zero_smul]; apply Fine.empty
 have hz:=Fine.seed (s:=X) i (mfree h hx); rw [show (Reed.think X).term i= put i from if_pos (mfree p hx)] at hz; exact hz.scale _ -- tune
lemma take_here{X Y:Finset m}{x:Ket m} (p:acts (cutM X) x=0)(h:acts (cutM Y) x=x): Fine X Y true (remove x):=by
 rw [remove_def]; refine Fine.sumF _ _ ?_; intro i _; by_cases hx:x.ofLp i=0; rw [hx,star_zero,zero_smul]; apply Fine.empty
 have hz:=Fine.seed (s:=X) i (mfree h hx); rw [show (Reed.think X).term i= -takeF i from if_neg (fun v=>hx (reach_e p v))] at hz; exact (show Fine X Y true (takeF i) from (by simpa using hz.scale (-1))).scale _
lemma port_here {x: Ket (Single N)}(h:acts (cutM (modes W)) x=x)(p:okSpin b x):Snow W true (port b x):=by unfold okSpin at p; rw [touchP] at p; cases b; exact take_here p h; exact put_here p h
variable (i: Axis)
def Cross (X:FC (Single N))(F:Obs P):Prop:= ∀ U: Nom N P,IsUnit (Peaks.cloth j M G (unionP U))→∀ z:Phys P, acts X (prog G j M Q U z)=prog G j M Q U (acts (F U.1) z)
def beamCL (Q:SpaceM)(X:Nom N P): Phys P →L[ℂ]Phys N:=
 let A:= ticketT (Thread j) true M G (unionP X); let f: Phys P →L[ℂ] Wave (Iota G):= Fock.hoist (switchG G).symm.toEmbedding ∅
 let L:=exp (-(plankP N Q.val)); let s:= (sect0 G*chargeA (Thread j) G M (unionP X))⁻¹; let F:=s • ((pailL (patchQ G) (reefS G true)).comp ((acts (quant A)).comp f)); (skyGlow (mateK N) L (mateK N))⁻¹ • ((acts (quant L)).comp F)
lemma programB (Q:SpaceM)(X:Nom N P)(p:Phys P): prog G j M Q X p= beamCL G j M Q X p:= rfl
variable {G Q M j} {F V:Obs P}
namespace Cross
lemma add (p:Cross G j Q M A F)(v:Cross G j Q M A' V): Cross G j Q M (A+A') (F+V):=by intro t s x; rw [act_add,Pi.add_apply,act_add,p t s x,v t s x,programB,programB,programB,map_add]
lemma mul (p:Cross G j Q M A F)(v:Cross G j Q M A' V): Cross G j Q M (A*A') (F*V):=by intro t s x; rw [act_mul,Pi.mul_apply,act_mul,v t s x,p t s]
lemma smul (v:ℂ)(p:Cross G j Q M A F):Cross G j Q M (v•A) (v•F):=by intro t s x; rw [act_smul,p t s x,Pi.smul_apply,act_smul,programB,programB,map_smul]
end Cross
local notation "fθ" =>Fixed.reflectTest
lemma mirQ (V:Obs P): fθ i false V= fun U=>theta (Fixed.reflectP P i) (V (Fixed.reflConfig P i U)):=by ext1 x; exact one_smul ..
structure Meet (X:Support (More P))(b:Bool)(L:FC (Single N))(G:Ratio N P)(j:ℕ)(M:Male)(Q:SpaceM)(i:Axis)(F:Obs P): Prop where
 cont:Continuous F
 y:LocalOn X F
 t:∀ U,Snow X b (F U)
 p:Cross G j Q M L F
 q:Cross G j Q M (theta (Fixed.reflectP N i) L) (Fixed.reflectTest i false F)
variable {i} {X:Support (More P)}{c:Bool}
namespace Meet
lemma add (p:Meet X b A G j M Q i F)(v:Meet X b A' G j M Q i V):Meet X b (A+A') G j M Q i (F+V):=⟨p.cont.add v.cont,fun U W t=>congrArg₂ (·+·) (p.y U W t) (v.y U W t), fun U=>Fine.add (p.t U) (v.t U),p.p.add v.p,(by rw [theta_add,Fixed.reflectTest_add]; exact p.q.add v.q)⟩
lemma mul (p:Meet X b A G j M Q i F)(v:Meet X c A' G j M Q i V): Meet X (b.xor c) (A*A') G j M Q i (F*V):=⟨p.cont.mul v.cont,fun U W t=>congrArg₂ (·*·) (p.y U W t) (v.y U W t), fun U=>Fine.grow (p.t U) (v.t U),p.p.mul v.p,(by rw [theta_mul,show fθ i false (F*V)=fθ i false F*fθ i false V by rw [mirQ,mirQ,mirQ]; ext1 x; rw [Pi.mul_apply,theta_mul]; rfl]; exact p.q.mul v.q)⟩
lemma smul (p:Meet X b A G j M Q i F)(v:ℂ): Meet X b (v•A) G j M Q i (v•F):=⟨continuous_const.smul p.cont,fun U W t=>congrArg (v • ·) (p.y U W t),fun U=>Fine.scale (p.t U) v, p.p.smul _,by rw [theta_smul, Fixed.reflectTest_smul]; exact p.q.smul _⟩
end Meet
variable (G Q M i j) {k:ℕ} (o:Odd G.count.val)(v:SetK j G.count k)
include o v
local notation "Rψ"=> reach G W (units G.count k)
lemma snow_p (h:Snow W b A):∃ V,Meet Rψ b A G j M Q i V:=by
 change Fine (Tset _) (modes W) b A at h
 induction h with
 | empty b=> refine ⟨0,continuous_const,fun _ _ _=>rfl,fun _=>Fine.empty _,fun U t p=>by rw [act_zero,Pi.zero_apply,act_zero,programB,map_zero],?_⟩; rw [theta_zero,mirQ]; intro t s x; simp only [Pi.zero_apply,theta_zero,programB]; rw [act_zero,act_zero,map_zero]
 | one=> exact ⟨1,continuous_const,fun _ _ _=> rfl,fun _=> Fine.one,(fun t s x=> (by simp)), by rw [Fixed.reflectOne,theta_one]; intro t s x; simp⟩ -- tune
 | seed x a=>
   let u:=basisKet x; let f (b:Bool)(U):= songL G j M Q b U u; let F(b:Bool)(U):= port b (f b U); have hZ: acts (cutM (modes W)) u=u:= (cut_basis ..).trans (if_pos a)
   have hz(b:Bool)(v':okSpin b u):Meet Rψ true (port b u) G j M Q i (F b):=by
      have he:= song_c G j Q M o v b u; refine ⟨?_,fun U V h=> congrArg (port b) (reach_p G j Q M o v b hZ U V h),fun U=> port_here (carrierL G j Q M o v b hZ U) (spinG G j Q M o b v' U), fun X x' z=> pro_p G j M X Q b v' o x' z,(by rw [mirQ]; exact fun y k u=> pro_mir G j Q M i y o b v' k u)⟩
      cases b; exact (continuous_star.comp ((create (n:=Single P)).continuous_of_finiteDimensional.comp he)); exact ((create (n:=Single P)).continuous_of_finiteDimensional.comp he)
   by_cases p:x∈Tset N
   · rw [show (Reed.think _).term _=put x from if_pos p,← create_put]; exact ⟨F true,hz true ((by rw [okSpin,touchP]; exact (cut_basis ..).trans (if_pos p)))⟩
   rw [show (Reed.think _).term _= -takeF x from if_neg p,← remove_take]; have he:okSpin false u:=by rw [okSpin,touchP]; exact (cut_basis ..).trans (if_neg p)
   exact ⟨(-1:ℂ) • F false,(by rw [←neg_one_smul ℂ]; exact (hz false he).smul _)⟩
 | add _ _ i j=> obtain ⟨U,p⟩:=i; obtain ⟨V,t⟩:=j; exact ⟨_,p.add t⟩
 | grow _ _ i j=> obtain ⟨U,p⟩:=i; obtain ⟨V,t⟩:=j; exact ⟨_,p.mul t⟩
 | scale _ _ i=> obtain ⟨U,p⟩:=i; exact ⟨_,p.smul _⟩
end Leg
end YM.CF.BProof.Bide
