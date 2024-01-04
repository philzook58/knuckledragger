from setuptools import setup, find_packages

setup(
    name="knuckledragger",
    version="0.1.1",
    author="Philip Zucker",
    author_email="phlzook58@gmail.com",
    description="Interactive Theorem Prover",
    long_description=open("README.md").read(),
    long_description_content_type="text/markdown",
    url="https://github.com/philzook58/knuckledragger",
    packages=find_packages(),
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    install_requires=["z3-solver"],
    extras_require={
        "dev": [
            "pytest>=6.0",
        ],
    },
)
