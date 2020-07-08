# -*- mode: ruby -*-
# vi: set ft=ruby :

$apt = <<SCRIPT
export DEBIAN_FRONTEND=noninteractive 

apt-get update -y
apt-get install -y python3-dev # pip & cryptodomex
apt-get install -y build-essential libgmp-dev libmpfr-dev libmpc-dev # gmpy2

SCRIPT

$cryptopal = <<SCRIPT
python3 -m venv cryptopalenv --without-pip
source cryptopalenv/bin/activate
wget --quiet -O - https://bootstrap.pypa.io/get-pip.py | python3
python3 -m pip install requests pycryptodomex PyCrypto gmpy2
python3 /vagrant/cryptopal.py -v

SCRIPT

Vagrant.configure(2) do |config|
  config.vm.box = "ubuntu/bionic64"
  config.vm.box_check_update = false
 
  # prevent TTY error messages
  config.ssh.shell = "bash -c 'BASH_ENV=/etc/profile exec bash'"

  config.vm.provision "shell",
                      inline: $apt,
                      preserve_order: true,
                      privileged: true 

  config.vm.provision "shell",
                      inline: $cryptopal,
                      preserve_order: true,
                      privileged: false
end
