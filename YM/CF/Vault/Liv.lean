import YM.CF.Vault.Saul
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(p:1≤j)
abbrev rawX(j:ℕ): Chop Male:= mateF (@Peaks.cloth j)
section
variable {N P:Side}(G:Ratio N P)(h:G.count=L)
include hj h ho
lemma raw_h (i): rawX j i G (vacancyY N P)*helmC G=helmC G*cc (rawX j i G (vacancyY N P)):=by
 let T:=Peaks.cloth j i G; have he:T 1= _:= (canUse j L ho).fixed i G h; have ht:Odd G.count.val:=h.symm ▸ ho
 unfold T at he; unfold rawX mateF; rw [still_u,he]; unfold helmC; rw [cart_traded (cBrix j _ ht),op_kron_mul,op_cc_kron,op_kron_mul,cc_one,one_mul,mul_one,posed j ht,(bT j).eq]
lemma dust_id (i:Duel): vacantR G i (A:=dustX j)=vacantR G i.1 (A:=rawX j):=by
 apply version i G _ _ (rawX j) (helmC G) (helmC G) (raw_h j L ho hj G h i.1).symm _ (helm_eq G true) (helm_eq G false); rw [← helm_eq G true]; exact (unit_square G true (1,vacuumW P,vacuumW N))
lemma fade_at (b:Bool)(i:Duel): vacantR G i (A:=fade j b)=ticketT (@Peaks.cloth j) b i.1 G (vacancyY N P).1:=by
 unfold vacantR; rw [show fade j b i G (vacancyY N P)=fort _ _ from duskF G j i (1,vacuumW P,vacuumW N) b]; change fort _ (dustX j i G (vacancyY N P))=_; rw [show dustX j i G _=_ from dust_id j L ho hj G h i]; rw [fort,ticketT]; rw [show icec (vacancyY N P).1=(vacancyY N P).1 from revI 1]; rfl
end
lemma overStill {ι:Type*}{L:Side}{P Q:Chop ι}{u v:AxisT}(h:BoxD L u v P)(p:BoxD L v u Q)(t:Still L fun G x=>∀ i, P i G (vacancyY _ _)*Q i G (vacancyY _ _)=1): BoxD L v u (fun i _ _ G x=> (P i G x)⁻¹)∧ Still L (fun G x=>∀ i,IsUnit (P i G (post x))):=by
 obtain ⟨C,p,H⟩:=p.assets; obtain ⟨k,Y⟩:= (H.gilded.plus t).stamp
 obtain ⟨a,b⟩:=ocean h C (k:=k) (fun i _ _ G h v=> ⟨Q i G (vacancyY _ _),(Y G h v).2 i,(Y G h v).1 i⟩); exact ⟨a,(interest_g b).gilded⟩
lemma boldX {ι:Type*}(b k:Bool): BoxD L (ℒ b) (ℒ b) (lendX k (ι:=ι)):=by
 obtain ⟨a,c,e,h,g,w,v,V⟩:= BoxD.marked (gradeBudget L (ι:=Male) b k); exact boxify (k:=v) (fun i N P G t u=> V ⟨1,odd_one⟩ G t u) h w -- tune
include ho hj
lemma stable_j : BoxD L (ℒ false) (ℒ true) (fun i _ _ G x=>(dustX j i G x)⁻¹)∧ BoxD L (ℒ true) (ℒ false) (dustX j) ∧ Still L (fun G x=>∀ i,IsUnit (dustX j i G (post x))):=by
 let V:=@Peaks.cloth j; let h:= canUse j L ho
 have hp : BoxD L (ℒ true) (ℒ false) (dustX j):=twist_X (BoxD.marked h.expense) (tablesB Male true L ho) (tablesB Male false L ho)
 obtain ⟨hs,p⟩:=useK j L hj ho h
 let X:Chop Duel:=fun i _ _ G x=> (V i.1 G x.1)⁻¹
 have hv : BoxD L (ℒ false) (ℒ true) X:= (BoxD.marked hs).reindex Prod.fst
 have he:Still L (fun G x=>∀ i:Duel,dustX j i G (vacancyY _ _)*X i G (vacancyY _ _)=1):=by
   obtain ⟨e,t,v,H⟩:=p; refine ⟨1,one_pos,v,fun {N P} G h s' x hg i=>?_⟩
   rw [show dustX j i G _=_ from dust_id j L ho hj G h i]; let A:=V i.1 G (vacancyY N P).1; change A*A⁻¹=1; unfold A; rw [still_u]; exact (Fock.live (H G h s' 1 (crests G e t) i.1)).1
 obtain ⟨h,hK⟩:= overStill hp hv he; exact ⟨h,hp,hK⟩
lemma fade_cost (b:Bool) : BoxD L (ℒ false) (ℒ true) (fade j b):=by obtain ⟨f,h,k⟩:= stable_j j L ho hj; exact (f.chain (boldX L true b)).add (h.balm.chain (BoxD.one.sub (boldX L true b)))
end YM.CF.Vault
